#!/usr/bin/env python3
"""
SkariorObf Universal Deobfuscator v1.0

Автоматически снимает все слои обфускации SkariorObf:
  - XOR шифрование строк/чисел
  - AST мусорный код (MemoryError, ZeroDivisionError, match/case)
  - Тернарные выражения varsobf
  - Извлечение payload compile-режима (base64->zlib->lzma->gzip->marshal)
  - Анти-дебаг, проверки автора, анти-pycdc артефакты
  - Заголовок и определения деобфускаторных функций

Использование: python deobf_skarior_universal.py <input.py> [output.py]
"""

import ast, re, sys, os, marshal, lzma, gzip, zlib, base64, dis
import types, itertools, subprocess, tempfile


# ──────────────────────────────────────────────────────────────
# XOR ДЕШИФРОВКА
# ──────────────────────────────────────────────────────────────

def find_xor_key(code):
    """Ищет XOR-ключ по паттерну chr(ord(c) ^ KEY)."""
    m = re.search(r'chr\(ord\(\w+\)\s*\^\s*(\d+)\)\s*for\s+\w+\s+in', code)
    if m:
        return int(m.group(1))
    return None


def find_deobf_funcs(code):
    """Ищет имена функций-дешифраторов строк и чисел."""
    str_func = num_func = None
    for m in re.finditer(r'def\s+(\w+)\s*\(\w+\)\s*:', code):
        name = m.group(1)
        chunk = code[m.start():m.start() + 600]
        if 'join' in chunk and 'chr' in chunk and 'ord' in chunk:
            str_func = name
        elif 'isinstance' in chunk and 'int' in chunk and str_func != name:
            num_func = name
        if str_func and num_func:
            break
    return str_func, num_func


class XORDecryptor(ast.NodeTransformer):
    """Заменяет вызовы XOR-дешифраторов на расшифрованные значения."""

    def __init__(self, key, str_func, num_func):
        self.key, self.str_func, self.num_func = key, str_func, num_func

    def visit_Call(self, node):
        self.generic_visit(node)
        if not isinstance(node.func, ast.Name) or len(node.args) != 1:
            return node
        arg = node.args[0]
        if not isinstance(arg, ast.Constant):
            return node

        if node.func.id == self.str_func and isinstance(arg.value, str):
            return ast.Constant(value=''.join(chr(ord(c) ^ self.key) for c in arg.value))
        if node.func.id == self.num_func:
            if isinstance(arg.value, int):
                return ast.Constant(value=arg.value ^ self.key)
            if isinstance(arg.value, float):
                return ast.Constant(value=arg.value - self.key)
        return node


# ──────────────────────────────────────────────────────────────
# РАЗРЕШЕНИЕ EVAL И ОТСЛЕЖИВАНИЕ АЛИАСОВ
# ──────────────────────────────────────────────────────────────

class EvalResolver(ast.NodeTransformer):
    def visit_Call(self, node):
        self.generic_visit(node)

        if isinstance(node.func, ast.Name) and node.func.id == 'eval':
            if len(node.args) == 1 and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str):
                return ast.Name(id=node.args[0].value, ctx=ast.Load())

        if isinstance(node.func, ast.Name) and node.func.id == 'chr':
            if len(node.args) == 1 and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, int):
                return ast.Constant(value=chr(node.args[0].value))

        return node


def _try_eval_const(node):
    """Статическое вычисление константного выражения (конкатенация chr и т.д.)."""
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left = _try_eval_const(node.left)
        right = _try_eval_const(node.right)
        if isinstance(left, str) and isinstance(right, str):
            return left + right
    return None


class ConcatFolder(ast.NodeTransformer):
    """Сворачивает chr(N)+chr(N)+... и 'a'+'b'+... в константные строки."""

    def visit_BinOp(self, node):
        self.generic_visit(node)
        val = _try_eval_const(node)
        if isinstance(val, str):
            return ast.Constant(value=val)
        return node


def build_alias_map(tree):
    """Находит присваивания OBFNAME = builtin и строит карту замен."""
    aliases = {}
    for stmt in tree.body:
        if not isinstance(stmt, ast.Assign) or len(stmt.targets) != 1:
            continue
        target = stmt.targets[0]

        if isinstance(target, ast.Name) and isinstance(stmt.value, ast.Name):
            if stmt.value.id in BUILTIN_NAMES and target.id not in BUILTIN_NAMES:
                aliases[target.id] = stmt.value.id

        if isinstance(target, ast.Tuple) and isinstance(stmt.value, ast.Tuple):
            if len(target.elts) == len(stmt.value.elts):
                for t, v in zip(target.elts, stmt.value.elts):
                    if (isinstance(t, ast.Name) and isinstance(v, ast.Name) and
                            v.id in BUILTIN_NAMES and t.id not in BUILTIN_NAMES):
                        aliases[t.id] = v.id

        if isinstance(target, ast.Name) and isinstance(stmt.value, ast.Call):
            if (isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == 'eval' and
                    len(stmt.value.args) == 1 and isinstance(stmt.value.args[0], ast.Constant) and
                    isinstance(stmt.value.args[0].value, str)):
                resolved = stmt.value.args[0].value
                if target.id not in BUILTIN_NAMES:
                    aliases[target.id] = resolved
    return aliases


class AliasReplacer(ast.NodeTransformer):
    """Заменяет обфусцированные имена переменных на их builtin-эквиваленты."""

    def __init__(self, aliases):
        self.aliases = aliases

    def visit_Name(self, node):
        if node.id in self.aliases:
            node.id = self.aliases[node.id]
        return node

    def visit_Subscript(self, node):
        self.generic_visit(node)
        return node


# ──────────────────────────────────────────────────────────────
# УДАЛЕНИЕ МУСОРНОГО КОДА ИЗ AST
# ──────────────────────────────────────────────────────────────

def _is_args0_eq(test, value):
    """Проверяет паттерн e.args[0] == value в условии."""
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1 and
            isinstance(test.ops[0], ast.Eq) and len(test.comparators) == 1):
        return False
    cmp = test.comparators[0]
    if not (isinstance(cmp, ast.Constant) and cmp.value == value):
        return False
    left = test.left
    return (isinstance(left, ast.Subscript) and
            isinstance(left.value, ast.Attribute) and left.value.attr == 'args' and
            isinstance(left.slice, ast.Constant) and left.slice.value == 0)


def _extract_real(handler_body):
    """Извлекает реальный код из обработчика MemoryError (ветка e.args[0] == 1)."""
    real = []
    for s in handler_body:
        if isinstance(s, ast.If) and _is_args0_eq(s.test, 1):
            real.extend(s.body)
    return real or None


def _find_memoryerror_block(stmts):
    """Ищет паттерн: x=0; x+=1; try/except MemoryError с настоящим кодом внутри."""
    for i in range(len(stmts) - 2):
        s0, s1, s2 = stmts[i], stmts[i + 1], stmts[i + 2]
        if not (isinstance(s0, ast.Assign) and isinstance(s1, ast.AugAssign) and isinstance(s2, ast.Try)):
            continue
        if not (len(s0.targets) == 1 and isinstance(s0.value, ast.Constant) and s0.value.value == 0):
            continue
        if not (isinstance(s1.op, ast.Add) and isinstance(s1.value, ast.Constant) and s1.value.value == 1):
            continue
        if not (len(s2.handlers) == 1 and isinstance(s2.handlers[0].type, ast.Name) and
                s2.handlers[0].type.id == 'MemoryError'):
            continue
        real = _extract_real(s2.handlers[0].body)
        if real is not None:
            return stmts[:i] + real + stmts[i + 3:]
    return None


def _is_dead_cond(test):
    """Проверяет, является ли условие всегда ложным (мёртвый код)."""
    if not isinstance(test, ast.Compare) or len(test.ops) != 1 or len(test.comparators) != 1:
        return False
    left, cmp = test.left, test.comparators[0]
    if isinstance(test.ops[0], ast.Eq):
        if (isinstance(left, ast.Constant) and isinstance(left.value, str) and
                isinstance(cmp, ast.Constant) and isinstance(cmp.value, str)):
            return left.value != cmp.value
    if isinstance(test.ops[0], ast.Gt):
        if (isinstance(left, ast.Constant) and isinstance(left.value, (int, float)) and
                isinstance(cmp, ast.Constant) and isinstance(cmp.value, (int, float))):
            return not (left.value > cmp.value)
    return False


def clean_body(body):
    """Рекурсивная очистка тела блока от мусорного кода."""
    changed = True
    while changed:
        changed = False
        result = _find_memoryerror_block(body)
        if result is not None:
            body = result
            changed = True
            continue
        new_body = []
        for stmt in body:
            processed = _clean_stmt(stmt)
            new_body.extend(processed)
            if len(processed) != 1 or (processed and processed[0] is not stmt):
                changed = True
        body = new_body
    return body


def _clean_stmt(stmt):
    """Очищает одно выражение AST от мусора."""
    if isinstance(stmt, ast.Try):
        return _handle_try(stmt)

    if isinstance(stmt, ast.Match):
        return []

    if isinstance(stmt, ast.If):
        stmt.body = clean_body(stmt.body)
        stmt.orelse = clean_body(stmt.orelse) if stmt.orelse else []
        if _is_dead_cond(stmt.test):
            return stmt.orelse if stmt.orelse else []
        return [stmt]

    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        stmt.body = clean_body(stmt.body)
        return [stmt]

    if isinstance(stmt, (ast.For, ast.While)):
        stmt.body = clean_body(stmt.body)
        stmt.orelse = clean_body(stmt.orelse) if stmt.orelse else []
        return [stmt]

    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        stmt.body = clean_body(stmt.body)
        return [stmt]

    if isinstance(stmt, ast.ClassDef):
        stmt.body = clean_body(stmt.body)
        return [stmt]

    if isinstance(stmt, ast.Expr):
        v = stmt.value
        if isinstance(v, ast.Call) and isinstance(v.func, ast.Name):
            if v.func.id in ('str', 'int') and len(v.args) == 1 and isinstance(v.args[0], ast.Constant):
                return []
        if isinstance(v, ast.Constant) and isinstance(v.value, str):
            return []

    return [stmt]


def _handle_try(node):
    """Обрабатывает try/except блоки: извлекает настоящий код из ZeroDivisionError/MemoryError обёрток."""
    for h in node.handlers:
        if isinstance(h.type, ast.Name) and h.type.id == 'ZeroDivisionError':
            return clean_body(h.body)

    for h in node.handlers:
        if isinstance(h.type, ast.Name) and h.type.id == 'MemoryError':
            has_match = any(isinstance(s, ast.Match) for s in node.body)
            has_raise = any(
                isinstance(s, ast.Raise) and isinstance(getattr(s, 'exc', None), ast.Call) and
                isinstance(s.exc.func, ast.Name) and s.exc.func.id == 'MemoryError'
                for s in node.body)
            if has_match or has_raise:
                return clean_body(h.body)

    if (all(isinstance(s, ast.Pass) for s in node.body) and
            all(isinstance(s, ast.Pass) for h in node.handlers for s in h.body)):
        return []

    node.body = clean_body(node.body)
    for h in node.handlers:
        h.body = clean_body(h.body)
    node.orelse = clean_body(node.orelse) if node.orelse else []
    node.finalbody = clean_body(node.finalbody) if node.finalbody else []
    return [node]


# ──────────────────────────────────────────────────────────────
# УПРОЩЕНИЕ VARSOBF (ТЕРНАРНЫЕ ВЫРАЖЕНИЯ)
# ──────────────────────────────────────────────────────────────

class VarsobfSimplifier(ast.NodeTransformer):
    """Упрощает (X) if bool(Y) else X → X, когда обе ветки идентичны."""

    def visit_IfExp(self, node):
        self.generic_visit(node)
        if ast.dump(node.body) == ast.dump(node.orelse):
            return node.orelse
        return node


# ──────────────────────────────────────────────────────────────
# COMPILE РЕЖИМ
# ──────────────────────────────────────────────────────────────

def extract_bytes_literals(code):
    """Извлекает байтовые литералы (потенциальные части payload) из кода."""
    lits = []
    try:
        tree = ast.parse(code)
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, bytes) and len(node.value) > 100:
                lits.append(node.value)
    except SyntaxError:
        for m in re.finditer(r"b'((?:[^'\\]|\\.)*)'", code):
            try:
                val = ast.literal_eval("b'" + m.group(1) + "'")
                if len(val) > 100:
                    lits.append(val)
            except Exception:
                pass
    return lits


def try_decode_compile(parts):
    """Пробует все комбинации/перестановки байтовых частей через цепочку base64->zlib->lzma->gzip->marshal."""
    parts.sort(key=len, reverse=True)
    top = parts[:min(len(parts), 6)]

    for n in (4, 3, 5, 6):
        if len(top) < n:
            continue
        for combo in itertools.combinations(top, n):
            for perm in itertools.permutations(combo):
                combined = b''.join(perm)
                try:
                    d = base64.b64decode(combined)
                    d = zlib.decompress(d)
                    d = lzma.decompress(d)
                    d = gzip.decompress(d)
                    co = marshal.loads(d)
                    if isinstance(co, types.CodeType):
                        return co
                except Exception:
                    continue
    return None


def decompile_code(co):
    """Декомпилирует code object через pycdc. Возвращает None если pycdc не справился."""
    raw = marshal.dumps(co)
    with tempfile.NamedTemporaryFile(suffix='.pyc', delete=False) as f:
        f.write(b'\xcb\x0d\r\n' + b'\x00' * 12 + raw)
        path = f.name
    try:
        r = subprocess.run(["D:\\pycdc.exe", path],
                           capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=30)
        if r.returncode == 0 and r.stdout.strip():
            lines = r.stdout.split('\n')
            while lines and (lines[0].startswith('#') or not lines[0].strip()):
                lines.pop(0)
            src = '\n'.join(lines)
            if 'WARNING: Decompyle incomplete' not in src or src.count('\n') > 30:
                return src
    except Exception:
        pass
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    return None


def _find_deobf_funcs_from_code(co):
    """Находит имена XOR-дешифраторов строк/чисел в code object по структуре вложенных функций."""
    str_func = num_func = None
    for c in co.co_consts:
        if not isinstance(c, types.CodeType):
            continue
        if not _is_obfuscated_name(c.co_name):
            continue
        if 'join' in c.co_names and str_func is None:
            str_func = c.co_name
        elif str_func and c.co_name != str_func and num_func is None:
            num_func = c.co_name
    return str_func, num_func


def find_xor_key_from_code(co):
    """Извлекает XOR-ключ из code object, ищет в константах функции-дешифратора."""
    for c in co.co_consts:
        if isinstance(c, types.CodeType) and 'join' in c.co_names:
            for v in c.co_consts:
                if isinstance(v, types.CodeType):
                    for cv in v.co_consts:
                        if isinstance(cv, int) and 2 <= cv <= 256:
                            return cv
            for v in c.co_consts:
                if isinstance(v, int) and 2 <= v <= 256 and v not in (0, 1):
                    return v
    return None


JUNK_STRS = frozenset({'0/0', 'decode', 'decompile', '100', '0', '1', 'return'})
JUNK_GLOBALS = frozenset({'ZeroDivisionError', 'MemoryError', 'ValueError'})


def _xor_decrypt_consts(co_obj, xor_key):
    """Расшифровывает строковые константы из code object, фильтрует мусор."""
    if xor_key is None:
        return []
    result = []
    for v in co_obj.co_consts:
        if isinstance(v, str) and len(v) > 0 and v != co_obj.co_name:
            dec = ''.join(chr(ord(c) ^ xor_key) for c in v)
            if dec.isprintable() and len(dec) > 1 and dec not in JUNK_STRS:
                result.append(dec)
    return result


def _clean_globals(co_obj):
    """Извлекает чистые имена глобальных переменных из code object."""
    return [n for n in co_obj.co_names
            if not _is_obfuscated_name(n) and n not in JUNK_GLOBALS
            and not (n.startswith('_') and n[1:].isdigit())]


def _format_signature(args, defaults):
    """Форматирует сигнатуру функции с дефолтными значениями."""
    if not defaults:
        return ', '.join(args)
    n_plain = len(args) - len(defaults)
    parts = list(args[:n_plain])
    for arg, default in zip(args[n_plain:], defaults):
        parts.append(f'{arg}={repr(default)}')
    return ', '.join(parts)


def _format_func_body(co_obj, xor_key, indent='    ', xor_str_func=None, xor_num_func=None):
    """Форматирует тело функции: пытается декомпилировать bytecode, иначе показывает метаданные."""
    bc_lines = None
    if xor_str_func and xor_key is not None:
        bc_lines = _bc_decompile_func(co_obj, xor_key, xor_str_func, xor_num_func)

    if bc_lines:
        return [f'{indent}{line}' for line in bc_lines]

    lines = []
    local_vars = list(co_obj.co_varnames[co_obj.co_argcount:])
    strings = _xor_decrypt_consts(co_obj, xor_key)
    globals_used = _clean_globals(co_obj)

    if local_vars:
        lines.append(f'{indent}# Локальные: {", ".join(local_vars)}')
    if strings:
        lines.append(f'{indent}# Строки: {strings}')
    if globals_used:
        filtered = [g for g in globals_used if g not in ('str', 'int', 'bool', 'type', 'len', 'range', 'list', 'dict', 'tuple', 'set', 'print', 'isinstance', 'getattr', 'setattr', 'hasattr', 'super', 'None', 'True', 'False')]
        if filtered:
            lines.append(f'{indent}# Использует: {", ".join(filtered)}')
    lines.append(f'{indent}...')
    return lines


# ──────────────────────────────────────────────────────────────
# BYTECODE-ДЕКОМПИЛЯТОР (Python 3.12+ compile-режим)
# ──────────────────────────────────────────────────────────────

_BINOP_SYMBOLS = {0: '+', 1: '&', 2: '//', 3: '<<', 4: '@', 5: '*',
                  6: '%', 7: '|', 8: '**', 9: '>>', 10: '-', 11: '/',
                  12: '^', 13: '+=', 14: '&=', 15: '//=', 16: '<<=',
                  17: '@=', 18: '*=', 19: '%=', 20: '|=', 21: '**=',
                  22: '>>=', 23: '-=', 24: '/=', 25: '^='}


def _bc_decompile_func(co, xor_key, xor_str_func, xor_num_func):
    """Реконструирует тело функции из Python 3.12 bytecode, фильтруя SkariorObf-мусор."""

    def xdec_s(s):
        return ''.join(chr(ord(c) ^ xor_key) for c in s)

    def xdec_n(n):
        if isinstance(n, float):
            return n - xor_key
        return n ^ xor_key

    all_instrs = list(dis.get_instructions(co))

    _SKIP = frozenset(('RESUME', 'NOP', 'POP_EXCEPT', 'PUSH_EXC_INFO',
                        'CHECK_EXC_MATCH', 'RERAISE', 'JUMP_FORWARD',
                        'JUMP_BACKWARD', 'EXTENDED_ARG', 'PUSH_NULL'))
    stmts = []
    stack = []
    i = 0
    while i < len(all_instrs):
        inst = all_instrs[i]
        region = all_instrs
        op = inst.opname

        if op in _SKIP:
            i += 1
            continue

        # --- Junk: ZeroDivisionError / MemoryError ссылки ---
        if op == 'LOAD_GLOBAL' and _resolve_global_arg(inst) in ('ZeroDivisionError', 'MemoryError'):
            i += 1
            continue

        # --- Junk: str(num_deobf(N)) → пропуск ---
        if op == 'LOAD_GLOBAL' and _resolve_global_arg(inst) == 'str':
            ahead = region[i + 1:i + 6]
            if any(ai.opname == 'LOAD_GLOBAL' and _is_obfuscated_name(_resolve_global_arg(ai)) for ai in ahead):
                end_j = i + 1
                calls_seen = 0
                while end_j < len(region) and calls_seen < 2:
                    if region[end_j].opname == 'CALL':
                        calls_seen += 1
                    end_j += 1
                if end_j < len(region) and region[end_j].opname == 'POP_TOP':
                    end_j += 1
                i = end_j
                continue

        # --- LOAD_CONST ---
        if op == 'LOAD_CONST':
            stack.append(('const', inst.argval))

        # --- LOAD_FAST ---
        elif op in ('LOAD_FAST', 'LOAD_FAST_CHECK'):
            stack.append(('var', inst.argval))

        # --- LOAD_GLOBAL ---
        elif op == 'LOAD_GLOBAL':
            name = _resolve_global_arg(inst)
            if _is_obfuscated_name(name):
                stack.append(('obf_func', name))
            else:
                stack.append(('name', name))

        # --- LOAD_ATTR ---
        elif op == 'LOAD_ATTR':
            obj = stack.pop() if stack else ('name', '?')
            stack.append(('expr', f'{_se(obj)}.{inst.argval}'))

        # --- STORE_FAST ---
        elif op == 'STORE_FAST':
            val = stack.pop() if stack else None
            if val and val[0] != 'junk':
                stmts.append(f'{inst.argval} = {_se(val)}')

        # --- STORE_ATTR ---
        elif op == 'STORE_ATTR':
            obj = stack.pop() if stack else ('name', '?')
            val = stack.pop() if stack else ('name', '?')
            stmts.append(f'{_se(obj)}.{inst.argval} = {_se(val)}')

        # --- CALL: XOR дешифровка или обычный вызов ---
        elif op == 'CALL':
            argc = inst.argval
            args = []
            for _ in range(argc):
                args.append(stack.pop() if stack else ('name', '?'))
            args.reverse()
            func = stack.pop() if stack else ('name', '?')
            if stack and stack[-1] == ('const', None):
                stack.pop()

            if func[0] == 'obf_func' and func[1] == xor_str_func and len(args) == 1 and args[0][0] == 'const':
                stack.append(('const', xdec_s(args[0][1])))
            elif func[0] == 'obf_func' and func[1] == xor_num_func and len(args) == 1 and args[0][0] == 'const':
                stack.append(('const', xdec_n(args[0][1])))
            elif func[0] == 'obf_func':
                stack.append(('junk', None))
            else:
                arg_strs = [_se(a) for a in args]
                stack.append(('expr', f'{_se(func)}({", ".join(arg_strs)})'))

        # --- FORMAT_VALUE ---
        elif op == 'FORMAT_VALUE':
            val = stack.pop() if stack else ('name', '?')
            if val[0] == 'const' and isinstance(val[1], str):
                stack.append(('fstr_lit', val[1]))
            else:
                stack.append(('fstr_var', _se(val)))

        # --- BUILD_STRING → f-строка ---
        elif op == 'BUILD_STRING':
            count = inst.argval
            parts = []
            for _ in range(count):
                parts.append(stack.pop() if stack else ('fstr_lit', '?'))
            parts.reverse()
            fstr = ''
            for p in parts:
                if p[0] == 'fstr_lit':
                    fstr += str(p[1])
                elif p[0] == 'fstr_var':
                    fstr += '{' + str(p[1]) + '}'
                else:
                    fstr += '{' + _se(p) + '}'
            stack.append(('expr', f"f'{fstr}'"))

        # --- BUILD_LIST / BUILD_TUPLE / BUILD_MAP ---
        elif op == 'BUILD_LIST':
            elems = [stack.pop() if stack else ('name', '?') for _ in range(inst.argval)]
            elems.reverse()
            stack.append(('expr', f'[{", ".join(_se(e) for e in elems)}]'))

        elif op == 'BUILD_TUPLE':
            elems = [stack.pop() if stack else ('name', '?') for _ in range(inst.argval)]
            elems.reverse()
            # Junk: BUILD_TUPLE of obfuscated names followed by POP_TOP
            if all(e[0] in ('obf_func', 'junk') or (_is_obfuscated_name(_se(e)) if e[0] == 'name' else False) for e in elems):
                stack.append(('junk', None))
            else:
                stack.append(('expr', f'({", ".join(_se(e) for e in elems)})'))

        elif op == 'BUILD_MAP':
            pairs = []
            for _ in range(inst.argval):
                v = stack.pop() if stack else ('name', '?')
                k = stack.pop() if stack else ('name', '?')
                pairs.append(f'{_se(k)}: {_se(v)}')
            pairs.reverse()
            stack.append(('expr', '{' + ', '.join(pairs) + '}'))

        # --- BINARY_OP ---
        elif op == 'BINARY_OP':
            right = stack.pop() if stack else ('name', '?')
            left = stack.pop() if stack else ('name', '?')
            sym = _BINOP_SYMBOLS.get(inst.arg, '?')
            if sym.endswith('=') and len(sym) >= 2:
                base_sym = sym[:-1]
                stack.append(('expr', f'{_se(left)} {base_sym} {_se(right)}'))
            else:
                stack.append(('expr', f'{_se(left)} {sym} {_se(right)}'))

        # --- COMPARE_OP ---
        elif op == 'COMPARE_OP':
            right = stack.pop() if stack else ('name', '?')
            left = stack.pop() if stack else ('name', '?')
            stack.append(('expr', f'{_se(left)} {inst.argval} {_se(right)}'))

        # --- POP_JUMP_IF_FALSE → if ---
        elif op == 'POP_JUMP_IF_FALSE':
            cond = stack.pop() if stack else ('name', '?')
            cond_s = _se(cond)
            if 'decode' in cond_s and 'decompile' in cond_s:
                pass
            elif "'100'" in cond_s or "'0/0'" in cond_s:
                pass
            else:
                stmts.append(f'if {cond_s}:')

        elif op == 'POP_JUMP_IF_TRUE':
            cond = stack.pop() if stack else ('name', '?')
            cond_s = _se(cond)
            if 'decode' in cond_s or "'100'" in cond_s:
                pass
            else:
                stmts.append(f'if not ({_se(cond)}):')

        # --- RAISE ---
        elif op == 'RAISE_VARARGS':
            argc = inst.argval
            if argc == 1 and stack:
                exc = stack.pop()
                stmts.append(f'raise {_se(exc)}')
            elif argc == 0:
                stmts.append('raise')

        # --- RETURN ---
        elif op == 'RETURN_VALUE':
            val = stack.pop() if stack else None
            if val and val[0] != 'junk':
                s = _se(val)
                if s != 'None':
                    stmts.append(f'return {s}')

        elif op == 'RETURN_CONST':
            if inst.argval is not None:
                stmts.append(f'return {repr(inst.argval)}')

        # --- POP_TOP ---
        elif op == 'POP_TOP':
            if stack:
                val = stack.pop()
                if val[0] == 'expr' and '(' in val[1]:
                    stmts.append(val[1])

        # --- FOR loop ---
        elif op == 'GET_ITER':
            pass
        elif op == 'FOR_ITER':
            iterable = stack.pop() if stack else ('name', '?')
            loop_var = '_'
            for li in range(i + 1, min(i + 3, len(all_instrs))):
                if all_instrs[li].opname == 'STORE_FAST':
                    loop_var = all_instrs[li].argval
                    break
                elif all_instrs[li].opname == 'UNPACK_SEQUENCE':
                    parts = []
                    for ui in range(li + 1, min(li + 1 + all_instrs[li].argval, len(all_instrs))):
                        if all_instrs[ui].opname == 'STORE_FAST':
                            parts.append(all_instrs[ui].argval)
                    loop_var = ', '.join(parts) if parts else '_'
                    break
            stmts.append(f'for {loop_var} in {_se(iterable)}:')

        elif op == 'BINARY_SUBSCR':
            idx_val = stack.pop() if stack else ('const', '?')
            obj = stack.pop() if stack else ('name', '?')
            stack.append(('expr', f'{_se(obj)}[{_se(idx_val)}]'))

        elif op == 'STORE_SUBSCR':
            idx_val = stack.pop() if stack else ('const', '?')
            obj = stack.pop() if stack else ('name', '?')
            val = stack.pop() if stack else ('name', '?')
            stmts.append(f'{_se(obj)}[{_se(idx_val)}] = {_se(val)}')

        elif op == 'COPY':
            n = inst.argval
            if len(stack) >= n:
                stack.append(stack[-n])

        elif op == 'SWAP':
            n = inst.argval
            if len(stack) >= n:
                stack[-1], stack[-n] = stack[-n], stack[-1]

        elif op == 'UNPACK_SEQUENCE':
            pass

        elif op == 'CONTAINS_OP':
            right = stack.pop() if stack else ('name', '?')
            left = stack.pop() if stack else ('name', '?')
            op_str = 'not in' if inst.argval else 'in'
            stack.append(('expr', f'{_se(left)} {op_str} {_se(right)}'))

        i += 1

    # Фильтрация мусора и пост-обработка
    _JUNK_PATTERNS = ("if 'decode'", "if 'decompile'", "if ?:", "if None:",
                       "<obf>", "<junk>", "if 'return'", "<code object",
                       "if '0/0'", "if '100'")
    cleaned = []
    prev_assign_target = None
    for s in stmts:
        if any(p in s for p in _JUNK_PATTERNS):
            continue
        if s.strip() in ('?', 'None', '', '?()'):
            continue
        # Augmented assignment: "x = x + 1" → "x += 1"
        m_assign = re.match(r'^(.+?) = (.+)$', s)
        if m_assign:
            target = m_assign.group(1)
            value = m_assign.group(2)
            for op_sym in ('+', '-', '*', '/', '//', '%', '**', '|', '&', '^', '<<', '>>'):
                if value == f'{target} {op_sym} 1':
                    s = f'{target} {op_sym}= 1'
                    break
                elif value.startswith(f'{target} {op_sym} '):
                    rhs = value[len(f'{target} {op_sym} '):]
                    s = f'{target} {op_sym}= {rhs}'
                    break
        cleaned.append(s)
    return cleaned if cleaned else None


def _se(val):
    """Stack element → строковое представление."""
    if val is None:
        return 'None'
    tag, v = val
    if tag == 'const':
        return repr(v)
    if tag in ('var', 'name', 'expr'):
        return str(v)
    if tag == 'obf_func':
        return '<obf>'
    if tag == 'junk':
        return '<junk>'
    if tag in ('fstr_lit', 'fstr_var'):
        return str(v)
    return str(v)


def _resolve_global_arg(inst):
    """Извлекает имя из LOAD_GLOBAL (Python 3.12 формат может быть tuple)."""
    if isinstance(inst.argval, tuple):
        return inst.argval[1]
    return inst.argval


def exec_extract(co, xor_key, input_path='obfuscated.py', log=None, xor_str_func=None, xor_num_func=None):
    """Извлекает определения через exec code object в песочнице."""
    import builtins as _builtins
    import io as _io

    saved = {
        'os_exit': os._exit,
        'exit': getattr(_builtins, 'exit', None),
        'quit': getattr(_builtins, 'quit', None),
        'sys_exit': sys.exit,
        'settrace': sys.settrace,
        'stdout': sys.stdout,
    }

    os._exit = lambda *a, **kw: None
    _builtins.exit = lambda *a, **kw: None
    _builtins.quit = lambda *a, **kw: None
    sys.exit = lambda *a, **kw: None
    sys.settrace = lambda *a: None
    sys.stdout = _io.StringIO()

    ns = {'__builtins__': _builtins, '__name__': '__not_main__', '__file__': input_path}

    try:
        exec(co, ns)
        ok = True
    except Exception as e:
        ok = False
        if log:
            log(f"exec ошибка: {type(e).__name__}: {e}")
    finally:
        os._exit = saved['os_exit']
        _builtins.exit = saved['exit']
        _builtins.quit = saved['quit']
        sys.exit = saved['sys_exit']
        sys.settrace = saved['settrace']
        sys.stdout = saved['stdout']

    if not ok:
        return None

    out = []
    imports = []
    constants = []
    functions = []
    classes = []

    for name in sorted(ns):
        if name.startswith('__'):
            continue
        if _is_obfuscated_name(name):
            continue
        if name.startswith('_') and len(name) > 1 and name[1:].isdigit():
            continue

        val = ns[name]
        if isinstance(val, types.ModuleType):
            imports.append(val.__name__)
        elif isinstance(val, type):
            classes.append((name, val))
        elif isinstance(val, types.FunctionType):
            if getattr(val, '__module__', '') in ('dataclasses', 'functools', 'abc', 'typing'):
                continue
            functions.append((name, val))
        elif isinstance(val, (str, int, float, bytes)) and not isinstance(val, bool):
            constants.append((name, val))
        elif isinstance(val, (list, dict, tuple, set)):
            if len(repr(val)) < 300:
                constants.append((name, val))

    for mod in sorted(imports):
        out.append(f'import {mod}')
    if imports:
        out.append('')

    for name, val in constants:
        out.append(f'{name} = {repr(val)}')
    if constants:
        out.append('')

    for name, func in functions:
        co_f = func.__code__
        args = list(co_f.co_varnames[:co_f.co_argcount])
        sig = _format_signature(args, func.__defaults__)
        out.append(f'def {name}({sig}):')
        out.extend(_format_func_body(co_f, xor_key, xor_str_func=xor_str_func, xor_num_func=xor_num_func))
        out.append('')

    for name, cls in classes:
        is_dataclass = hasattr(cls, '__dataclass_fields__')

        if is_dataclass:
            out.append(f'@dataclass')
            out.append(f'class {name}:')
            for fname, fobj in cls.__dataclass_fields__.items():
                tname = fobj.type.__name__ if isinstance(fobj.type, type) else str(fobj.type)
                if fobj.default is not fobj.default_factory:
                    out.append(f'    {fname}: {tname} = {repr(fobj.default)}')
                else:
                    out.append(f'    {fname}: {tname}')
        else:
            out.append(f'class {name}:')
            methods_found = False
            for attr_name in sorted(dir(cls)):
                attr = getattr(cls, attr_name, None)
                if not isinstance(attr, types.FunctionType):
                    continue
                if _is_obfuscated_name(attr_name):
                    continue
                ALLOWED_DUNDERS = {'__init__', '__enter__', '__exit__', '__repr__', '__str__',
                                   '__len__', '__getitem__', '__setitem__', '__contains__',
                                   '__iter__', '__next__', '__new__', '__del__', '__call__'}
                if attr_name.startswith('__') and attr_name.endswith('__') and attr_name not in ALLOWED_DUNDERS:
                    continue
                methods_found = True
                co_m = attr.__code__
                m_args = list(co_m.co_varnames[:co_m.co_argcount])
                m_sig = _format_signature(m_args, attr.__defaults__)
                out.append(f'    def {attr_name}({m_sig}):')
                out.extend(_format_func_body(co_m, xor_key, indent='        ', xor_str_func=xor_str_func, xor_num_func=xor_num_func))
                out.append('')
            if not methods_found:
                out.append('    pass')
        out.append('')

    if not functions and not classes and not constants:
        return None

    return '\n'.join(out) + '\n'


def reconstruct_from_code(co, xor_key=None):
    """Статическая реконструкция из code object (fallback если exec не сработал)."""
    lines = []

    def xor_s(s):
        if xor_key is None:
            return s
        return ''.join(chr(ord(c) ^ xor_key) for c in s)

    user_funcs = []
    user_classes = []
    imports = set()

    for c in co.co_consts:
        if not isinstance(c, types.CodeType):
            continue
        name = c.co_name
        if _is_obfuscated_name(name) or name.startswith('<') or name == '___':
            continue

        for n in c.co_names:
            if n in ('math', 'os', 'sys', 'json', 're', 'hashlib', 'base64',
                     'datetime', 'random', 'socket', 'sqlite3'):
                imports.add(f'import {n}')

        args = list(c.co_varnames[:c.co_argcount])
        str_consts = _xor_decrypt_consts(c, xor_key)

        inner = [ic for ic in c.co_consts if isinstance(ic, types.CodeType)
                 and not _is_obfuscated_name(ic.co_name) and not ic.co_name.startswith('<')]

        if any(n in ('__init__', '__name__', '__module__', '__qualname__') for n in c.co_names):
            methods = []
            for ic in inner:
                m_args = list(ic.co_varnames[:ic.co_argcount])
                m_consts = _xor_decrypt_consts(ic, xor_key)
                methods.append((ic.co_name, m_args, m_consts))
            user_classes.append((name, methods))
        else:
            user_funcs.append((name, args, str_consts))

    for imp in sorted(imports):
        lines.append(imp)
    if imports:
        lines.append('')

    for name, args, consts in user_funcs:
        lines.append(f'def {name}({", ".join(args)}):')
        if consts:
            lines.append(f'    # Строковые константы: {consts}')
        lines.append('    ...')
        lines.append('')

    for name, methods in user_classes:
        lines.append(f'class {name}:')
        for mname, margs, mconsts in methods:
            lines.append(f'    def {mname}({", ".join(margs)}):')
            if mconsts:
                lines.append(f'        # Строковые константы: {mconsts}')
            lines.append('        ...')
            lines.append('')
        lines.append('')

    if not user_funcs and not user_classes:
        lines.append(f'# co_filename: {co.co_filename}')
        lines.append(f'# co_names: {[n for n in co.co_names if not _is_obfuscated_name(n)]}')

    return '\n'.join(lines) + '\n'


# ──────────────────────────────────────────────────────────────
# УДАЛЕНИЕ ШАБЛОННОГО КОДА
# ──────────────────────────────────────────────────────────────

MARKERS_ANTIDEBUG = ["Нет!? Пошёл ты тогда нахуй", "Рыцаря задержал",
                     "No!? Fuck you then", "holding up the knight",
                     ">> Detect [", "settrace", "extract_stack", "__module__"]
MARKERS_CHEAT = ["Don't try to cheat SkariorObf"]
MARKERS_ANTIPYCDC = ["я твою мать ебал", "i fuck your mother"]


def _contains_marker(node, markers):
    """Проверяет, содержит ли AST-узел маркерные строки/атрибуты."""
    for child in ast.walk(node):
        if isinstance(child, ast.Constant) and isinstance(child.value, str):
            for m in markers:
                if m in child.value:
                    return True
        if isinstance(child, ast.Attribute):
            for m in markers:
                if m == child.attr:
                    return True
    return False


_OBF_CHARS = frozenset('Oo' + chr(0x41E) + chr(0x43E))


def _is_obfuscated_name(name):
    """Проверяет, использует ли имя паттерн обфускации O/О (лат./кир.)."""
    if len(name) < 10:
        return False
    return all(c in _OBF_CHARS for c in name)


def _find_antidebug_funcs(tree):
    """Находит все анти-дебаг функции и их граф вызовов."""
    all_markers = MARKERS_ANTIDEBUG + MARKERS_CHEAT + MARKERS_ANTIPYCDC
    marked = set()
    obf_funcs = set()

    for stmt in tree.body:
        if isinstance(stmt, ast.FunctionDef):
            if _contains_marker(stmt, all_markers):
                marked.add(stmt.name)
            if _is_obfuscated_name(stmt.name):
                obf_funcs.add(stmt.name)

    antidebug = set(marked)
    changed = True
    while changed:
        changed = False
        for stmt in tree.body:
            if isinstance(stmt, ast.FunctionDef) and stmt.name not in antidebug:
                for child in ast.walk(stmt):
                    if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
                        if child.func.id in antidebug:
                            antidebug.add(stmt.name)
                            changed = True
                            break
    return antidebug


def remove_boilerplate(tree, str_func, num_func):
    """Удаляет шаблонный код: анти-дебаг, проверки автора, функции-дешифраторы."""
    all_markers = MARKERS_ANTIDEBUG + MARKERS_CHEAT + MARKERS_ANTIPYCDC
    antidebug_funcs = _find_antidebug_funcs(tree)

    funcs_to_remove = set(antidebug_funcs)
    if str_func:
        funcs_to_remove.add(str_func)
    if num_func:
        funcs_to_remove.add(num_func)

    new_body = []
    for stmt in tree.body:
        if _contains_marker(stmt, all_markers):
            continue
        if isinstance(stmt, ast.FunctionDef) and stmt.name in funcs_to_remove:
            continue

        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            f = stmt.value.func
            if isinstance(f, ast.Name) and f.id in antidebug_funcs:
                continue

        if isinstance(stmt, ast.Assign):
            is_antidebug_var = False
            for child in ast.walk(stmt):
                if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
                    if child.func.id in antidebug_funcs:
                        is_antidebug_var = True
                        break
            if is_antidebug_var:
                continue
            target = stmt.targets[0] if len(stmt.targets) == 1 else None
            if target and isinstance(target, ast.Name) and _is_obfuscated_name(target.id):
                val = stmt.value
                if isinstance(val, (ast.Set, ast.Dict)):
                    continue

        if isinstance(stmt, ast.ImportFrom) or (isinstance(stmt, ast.Import) and
                any(a.name in ('traceback',) for a in stmt.names)):
            has_user_import = any(a.name not in ('traceback', 'marshal', 'sys') for a in stmt.names)
            if not has_user_import and antidebug_funcs:
                continue

        if isinstance(stmt, ast.Try):
            if (len(stmt.body) == 1 and isinstance(stmt.body[0], ast.Raise) and
                    isinstance(getattr(stmt.body[0], 'exc', None), ast.Name) and
                    stmt.body[0].exc.id == 'ValueError' and
                    all(isinstance(s, ast.Pass) for h in stmt.handlers for s in h.body)):
                continue
            if (all(isinstance(s, ast.Pass) for s in stmt.body) and
                    all(isinstance(s, ast.Pass) for h in stmt.handlers for s in h.body) and
                    not stmt.orelse):
                continue

        new_body.append(stmt)
    tree.body = new_body
    return tree


# ──────────────────────────────────────────────────────────────
# ОБНАРУЖЕНИЕ И УДАЛЕНИЕ STUB-ПРИСВАИВАНИЙ
# ──────────────────────────────────────────────────────────────

BUILTIN_NAMES = {'bool', 'int', 'str', 'type', 'chr', 'eval', 'globals',
                 'vars', 'callable', 'bytes', '__import__', 'exec', 'compile',
                 'getattr', 'setattr', 'hasattr', 'isinstance', 'print', 'open',
                 'len', 'range', 'list', 'dict', 'tuple', 'set', 'map', 'filter'}


def remove_stub_assignments(tree):
    """Удаляет самоприсваивания (chr = chr) и алиасы обфусцированных имён к builtin."""
    new_body = []
    for stmt in tree.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
            target, val = stmt.targets[0], stmt.value

            if isinstance(target, ast.Name) and isinstance(val, ast.Name):
                if target.id == val.id:
                    continue
                if val.id in BUILTIN_NAMES and target.id not in BUILTIN_NAMES:
                    continue

            if isinstance(target, ast.Tuple) and isinstance(val, ast.Tuple):
                if len(target.elts) == len(val.elts):
                    if all(isinstance(t, ast.Name) and isinstance(v, ast.Name) and t.id == v.id
                           for t, v in zip(target.elts, val.elts)):
                        continue
                    if all(isinstance(t, ast.Name) and isinstance(v, ast.Name) and
                           v.id in BUILTIN_NAMES and t.id not in BUILTIN_NAMES
                           for t, v in zip(target.elts, val.elts)):
                        continue

        new_body.append(stmt)
    tree.body = new_body
    return tree


def remove_orphaned_obf(tree):
    """Удаляет осиротевшие вызовы/присваивания с обфусцированными именами без определений."""
    defined = set()
    for stmt in tree.body:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            defined.add(stmt.name)
        if isinstance(stmt, ast.Assign):
            for t in stmt.targets:
                if isinstance(t, ast.Name):
                    defined.add(t.id)
                if isinstance(t, ast.Tuple):
                    for e in t.elts:
                        if isinstance(e, ast.Name):
                            defined.add(e.id)

    new_body = []
    for stmt in tree.body:
        if isinstance(stmt, ast.Expr):
            v = stmt.value
            target_name = None
            if isinstance(v, ast.Call) and isinstance(v.func, ast.Name):
                target_name = v.func.id
            elif isinstance(v, ast.Name):
                target_name = v.id
            elif isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute):
                pass
            if target_name:
                is_obf = _is_obfuscated_name(target_name)
                in_def = target_name in defined
                if is_obf and not in_def:
                    continue

        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
            t = stmt.targets[0]
            if isinstance(t, ast.Name) and _is_obfuscated_name(t.id):
                used = False
                for other in tree.body:
                    if other is stmt:
                        continue
                    for child in ast.walk(other):
                        if isinstance(child, ast.Name) and child.id == t.id:
                            used = True
                            break
                    if used:
                        break
                if not used:
                    continue

        new_body.append(stmt)
    tree.body = new_body
    return tree


# ──────────────────────────────────────────────────────────────
# ГЛАВНЫЙ ДЕОБФУСКАТОР
# ──────────────────────────────────────────────────────────────

class SkariorDeobfuscator:
    def __init__(self, verbose=True):
        self.verbose = verbose

    def log(self, msg):
        if self.verbose:
            print(f"[*] {msg}")

    def deobfuscate_file(self, input_path, output_path=None):
        self._input_path = input_path
        with open(input_path, 'r', encoding='utf-8-sig') as f:
            code = f.read()
        self.log(f"Файл: {input_path} ({len(code)} символов, {code.count(chr(10)) + 1} строк)")

        result = self.deobfuscate(code)

        if output_path is None:
            base, ext = os.path.splitext(input_path)
            output_path = base + '_deobfuscated' + ext
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(result)
        self.log(f"Результат: {output_path} ({len(result)} символов, {result.count(chr(10)) + 1} строк)")
        return result

    def deobfuscate(self, code, depth=0):
        if depth > 5:
            self.log("Достигнута максимальная глубина рекурсии")
            return code

        prefix = "  " * depth

        code = re.sub(
            r"\n*Name\s*=\s*'[^']*'\s*\nAuthor\s*=\s*'[^']*'\s*\ngithub\s*=\s*'[^']*'\s*\n*",
            '\n', code
        ).strip()
        self.log(f"{prefix}Заголовок удалён")

        xor_key = find_xor_key(code)
        str_func, num_func = find_deobf_funcs(code)
        if xor_key is not None:
            self.log(f"{prefix}XOR-ключ: {xor_key}")
        if str_func:
            self.log(f"{prefix}Функция дешифровки строк: {str_func}")
        if num_func:
            self.log(f"{prefix}Функция дешифровки чисел: {num_func}")

        parts = extract_bytes_literals(code)
        if len(parts) >= 4:
            self.log(f"{prefix}Найдено {len(parts)} байтовых литералов - пробуем compile-режим...")
            co = try_decode_compile(parts)
            if co:
                self.log(f"{prefix}Payload compile-режима раскодирован ({co.co_filename})")
                src = decompile_code(co)
                if src:
                    self.log(f"{prefix}Внутренний код декомпилирован ({len(src)} символов)")
                    return self.deobfuscate(src, depth + 1)
                self.log(f"{prefix}pycdc не справился - запускаем runtime-извлечение")
                inner_key = find_xor_key_from_code(co)
                inner_str_func, inner_num_func = _find_deobf_funcs_from_code(co)
                result = exec_extract(co, inner_key,
                                      input_path=getattr(self, '_input_path', 'obfuscated.py'),
                                      log=self.log,
                                      xor_str_func=inner_str_func,
                                      xor_num_func=inner_num_func)
                if result:
                    self.log(f"{prefix}Runtime-извлечение успешно")
                    return result
                self.log(f"{prefix}Runtime не сработал - статическая реконструкция")
                return reconstruct_from_code(co, inner_key)

        try:
            tree = ast.parse(code)
        except SyntaxError as e:
            self.log(f"{prefix}Ошибка парсинга: {e}")
            return code

        if xor_key is not None and str_func:
            tree = XORDecryptor(xor_key, str_func, num_func).visit(tree)
            ast.fix_missing_locations(tree)
            self.log(f"{prefix}XOR расшифрован")

        prev = None
        for i in range(15):
            tree.body = clean_body(tree.body)
            tree = VarsobfSimplifier().visit(tree)
            aliases = build_alias_map(tree)
            if aliases:
                tree = AliasReplacer(aliases).visit(tree)
            tree = EvalResolver().visit(tree)
            tree = ConcatFolder().visit(tree)
            ast.fix_missing_locations(tree)
            cur = ast.dump(tree)
            if cur == prev:
                self.log(f"{prefix}Очистка сошлась за {i + 1} проходов")
                break
            prev = cur

        tree = remove_boilerplate(tree, str_func, num_func)
        tree = remove_stub_assignments(tree)
        tree = remove_orphaned_obf(tree)
        ast.fix_missing_locations(tree)

        try:
            code = ast.unparse(tree)
        except Exception:
            pass

        code = re.sub(r"\{'([^'{}\\]*)'\}", r'\1', code)
        code = re.sub(r'\{"([^"{}\\]*)"\}', r'\1', code)

        obf_pattern = r'^[O\u041Eo\u043E]{10,}\(?\)?\s*$'
        lines = code.split('\n')
        cleaned = []
        blanks = 0
        for line in lines:
            if not line.strip():
                blanks += 1
                if blanks <= 2:
                    cleaned.append(line)
            elif re.match(obf_pattern, line.strip()):
                continue
            else:
                blanks = 0
                cleaned.append(line)

        return '\n'.join(cleaned).strip() + '\n'


# ──────────────────────────────────────────────────────────────
# CLI
# ──────────────────────────────────────────────────────────────

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("SkariorObf Universal Deobfuscator v1.0")
        print(f"Использование: {sys.argv[0]} <input.py> [output.py]")
        sys.exit(1)

    inp = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else None

    d = SkariorDeobfuscator()
    result = d.deobfuscate_file(inp, out)

    print(f"\n{'=' * 60}")
    print("РЕЗУЛЬТАТ ДЕОБФУСКАЦИИ (первые 80 строк):")
    print('=' * 60)
    for line in result.split('\n')[:80]:
        print(line)
    if result.count('\n') > 80:
        print(f"... (всего {result.count(chr(10)) + 1} строк)")
