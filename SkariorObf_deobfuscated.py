import ast
import random
import sys
import os
import marshal,lzma,gzip,zlib,base64

if sys.version_info < (3, 10):
    print("Установи версию python 3.10 или выше / \nInstall python version 3.10 or higher")
    sys.exit()

# def __rd():
#     return str(random.randint(0x1E000000000, 0x7E000000000))

def __rd():
    length = 25
    return "".join(random.choice(["O", "О"]) for _ in range(length))

def _rd():
    return str(random.randint(0xFFFFF, 0xFFFFFFFFFFFF))


KEY = random.randint(0, 50)

_eval = __rd()
_chr =  __rd()
_bool = __rd()
_type = __rd()
_int = __rd()
_str = __rd()
_globals = __rd()
___import___ = __rd()


rd_names = [
__rd(), # 0
__rd(), # 1
__rd(), # 2
__rd(), # 3
__rd(), # 4
__rd(), # 5
__rd(), # 6
__rd(), # 7
__rd(), # 8
__rd(), # 9
__rd(), # 10
__rd(), # 11
__rd(), # 12
__rd(), # 13
__rd(), # 14
__rd(), # 15
__rd(), # 16
__rd(), # 17
]


def randomint():
    return "".join(__import__("random").sample([str(i) for i in range(1, 20)], k=2))


def varsobf(v):
    return f"""({(v)}) if {_bool}({_bool}({_bool}({(v)}))) < {_bool}({_type}({_int}({randomint()})>{_int}({randomint()})<{_int}({randomint()})>{_int}({randomint()}))) and {_bool}({_str}({_str}({randomint()})>{_int}({randomint()})<{_int}({randomint()})>{_int}({randomint()}))) > 2 else {v}"""

def varsobf2(v):
    return f"""({(v)}) if bool(bool(bool({(v)}))) < bool(type(int({randomint()})>int({randomint()})<int({randomint()})>int({randomint()}))) and bool(str(str({randomint()})>int({randomint()})<int({randomint()})>int({randomint()}))) > 2 else {v}"""


def obf_str(s):
    return "+".join(f"{_chr}({code})" for code in [ord(c) for c in s])


def _add_location(node, lineno=0, col_offset=0):
    node.lineno = lineno
    node.col_offset = col_offset
    return node


def _make_node(node_type, *args, **kwargs):
    lineno = kwargs.pop('lineno', 0)
    col_offset = kwargs.pop('col_offset', 0)
    node = node_type(*args, **kwargs)
    return _add_location(node, lineno, col_offset)


def _moreobf(tree):
    import random

    def rd():
        length = 25
        return "".join(random.choice(["O", "О"]) for _ in range(length))

    def junk(en, max_value):
        cases = []
        line = max_value + 1
        for i in range(random.randint(1, 5)):
            case_name = "__"+rd()
            case_body = [
                ast.If(
                    test=ast.Compare(
                        left=ast.Subscript(
                            value=ast.Attribute(
                                value=ast.Name(id=en), 
                                attr='args'
                            ), 
                            slice=ast.Constant(value=0)
                        ), 
                        ops=[ast.Eq()], 
                        comparators=[ast.Constant(value=line)]
                    ), 
                    body=[
                        ast.Assign(
                            targets=[ast.Name(id=case_name)], 
                            value=ast.Constant(value=random.randint(0xFFFFF, 0xFFFFFFFFFFFF)), 
                            lineno=None
                        )
                    ], 
                    orelse=[]
                )
            ]
            cases.extend(case_body)
            line += 1
        return cases

    def bl(body):
        var = rd()
        en = rd()

        tb = [
            ast.AugAssign(
                target=ast.Name(id=var), 
                op=ast.Add(), 
                value=ast.Constant(value=1)
            ),
            ast.Try(
                body=[
                    ast.Raise(
                        exc=ast.Call(func=ast.Name(id='MemoryError'), 
                                     args=[ast.Name(id=var)], 
                                     keywords=[])
                    )
                ],
                handlers=[
                    ast.ExceptHandler(
                        type=ast.Name(id='MemoryError'), 
                        name=en, 
                        body=[]
                    )
                ],
                orelse=[],
                finalbody=[]
            )
        ]
        
        for i in body:
            tb[1].handlers[0].body.append(
                ast.If(
                    test=ast.Compare(
                        left=ast.Subscript(
                            value=ast.Attribute(
                                value=ast.Name(id=en), 
                                attr='args'
                            ), 
                            slice=ast.Constant(value=0)
                        ), 
                        ops=[ast.Eq()], 
                        comparators=[ast.Constant(value=1)]
                    ), 
                    body=[i], 
                    orelse=[]
                )
            )
        
        tb[1].handlers[0].body.extend(junk(en, len(body) + 1))
        
        node = ast.Assign(
            targets=[ast.Name(id=var)], 
            value=ast.Constant(value=0), 
            lineno=None
        )
        
        return [node] + tb

    def _bl(node):
        olb = node.body

        var = rd()
        en = rd()

        tb = [
            ast.AugAssign(
                target=ast.Name(id=var), 
                op=ast.Add(), 
                value=ast.Constant(value=1)
            ),
            ast.Try(
                body=[
                    ast.Raise(
                        exc=ast.Call(func=ast.Name(id='MemoryError'), 
                                     args=[ast.Name(id=var)], 
                                     keywords=[])
                    )
                ],
                handlers=[
                    ast.ExceptHandler(
                        type=ast.Name(id='MemoryError'), 
                        name=en, 
                        body=[]
                    )
                ],
                orelse=[],
                finalbody=[]
            )
        ]
        for i in olb:
            tb[1].handlers[0].body.append(
                ast.If(
                    test=ast.Compare(
                        left=ast.Subscript(
                            value=ast.Attribute(
                                value=ast.Name(id=en), 
                                attr='args'
                            ), 
                            slice=ast.Constant(value=0)
                        ), 
                        ops=[ast.Eq()], 
                        comparators=[ast.Constant(value=1)]
                    ), 
                    body=[i], 
                    orelse=[]
                )
            )
        tb[1].handlers[0].body.extend(junk(en, len(olb) + 1))
        node.body = [
            ast.Assign(
                targets=[ast.Name(id=var)], 
                value=ast.Constant(value=0), 
                lineno=None
            )
        ] + tb
        return node
    def on(node):
        if isinstance(node, ast.FunctionDef):
            return _bl(node)
        return node
    nb = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            nb.append(on(node))
        elif isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            nb.extend(bl([node]))
        elif isinstance(node, ast.Expr):
            nb.extend(bl([node]))
        else:
            nb.append(node)
    tree.body = nb
    return tree


def __moreobf(x):
    return ast.unparse(_moreobf(ast.parse(x)))


def rd():
    length = 25
    return "".join(random.choice(["O", "О"]) for _ in range(length))


def _syntax(x):
    def v(node):
        if node.name:
            for statement in node.body:
                ten = ast.Try(
                    body=[ast.parse(f"{_eval}('0/0')"),ast.parse(f"""if "decode" == "decompile":{rd()},{rd()},{rd()},{rd()}\nelse:pass""")],
                    handlers=[
                        ast.ExceptHandler(
                            type=ast.Name(id='ZeroDivisionError', ctx=ast.Load()),
                            name=None,
                            body=[z(statement)]
                        )
                    ],
                    orelse=[],
                    finalbody=[]
                )
                node.body[node.body.index(statement)] = ten
            return node
    def z(statement):
        return ast.Try(
            body=[ast.parse(f"{_eval}('0/0')")],
            handlers=[
                ast.ExceptHandler(
                    type=ast.Name(id='ZeroDivisionError', ctx=ast.Load()),
                    name=None,
                    body=[statement]
                )
            ],
            orelse=[ast.Pass()],
            finalbody=[ast.parse("str(100)")]
        )
    tree = ast.parse(x)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            v(node)
    st = ast.unparse(tree)
    return st



def xor_obfuscate(s: str, key: int = KEY) -> str:
    return ''.join(chr(ord(c) ^ key) for c in s)



def generate_deobfuscator_func(key: int = KEY) -> str:
    return f"""
def {rd_names[17]}({rd_names[13]}):
    {rd_names[0]} = 0
    {rd_names[0]} += 1
    try:
        raise MemoryError({rd_names[0]})
    except MemoryError as {rd_names[1]}:
        if {rd_names[1]}.args[0] == 1:
            return ''.join((chr(ord({rd_names[14]}) ^ {key}) for {rd_names[14]} in {rd_names[13]}))
        if {rd_names[1]}.args[0] == 3:
            {rd_names[2]} = {_rd()}
        if {rd_names[1]}.args[0] == 4:
            {rd_names[3]} = {_rd()}
        if {rd_names[1]}.args[0] == 5:
            {rd_names[4]} = {_rd()}
        if {rd_names[1]}.args[0] == 6:
            {rd_names[5]} = {_rd()}

def {rd_names[16]}({rd_names[15]}):
    {rd_names[11]} = 0
    {rd_names[11]} += 1
    try:
        raise MemoryError({rd_names[11]})
    except MemoryError as {rd_names[12]}:
        if {rd_names[12]}.args[0] == 1:
            if isinstance({rd_names[15]}, int):return {rd_names[15]} ^ {key}
            elif isinstance({rd_names[15]}, float):return {rd_names[15]} - {key}
        if {rd_names[12]}.args[0] == 3:
            {rd_names[6]} = {_rd()}
        if {rd_names[12]}.args[0] == 4:
            {rd_names[7]} = {_rd()}
        if {rd_names[12]}.args[0] == 5:
            {rd_names[8]} = {_rd()}
        if {rd_names[12]}.args[0] == 6:
            {rd_names[9]} = {_rd()}
        if {rd_names[12]}.args[0] == 7:
            {rd_names[10]} = {_rd()}

"""



class StringObfuscator(ast.NodeTransformer):
    def __init__(self, key):
        self.key = key
        self.import_added = False

    def visit_Constant(self, node):
        if isinstance(node.value, str):
            obf_str = xor_obfuscate(node.value, self.key)
            new_node = ast.Call(
                func=ast.Name(id=rd_names[17], ctx=ast.Load()),
                args=[ast.Constant(value=obf_str)],
                keywords=[]
            )
            return new_node
        elif isinstance(node.value, int):
            obf_num = node.value ^ self.key
            new_node = ast.Call(
                func=ast.Name(id=rd_names[16], ctx=ast.Load()),
                args=[ast.Constant(value=obf_num)],
                keywords=[]
            )
            return new_node
        elif isinstance(node.value, float):
            obf_num = node.value + self.key
            new_node = ast.Call(
                func=ast.Name(id=rd_names[16], ctx=ast.Load()),
                args=[ast.Constant(value=obf_num)],
                keywords=[]
            )
            return new_node
        return node

    def visit_JoinedStr(self, node):
        new_values = []
        for value in node.values:
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                obf_str = xor_obfuscate(value.value, self.key)
                new_values.append(ast.FormattedValue(
                    value=ast.Call(
                        func=ast.Name(id=rd_names[17], ctx=ast.Load()),
                        args=[ast.Constant(value=obf_str)],
                        keywords=[]
                    ),
                    conversion=-1
                ))
            else:
                new_values.append(self.visit(value))
        return ast.JoinedStr(values=new_values)



def obfuscate_file(code, key = KEY):
    tree = ast.parse(code)
    obfuscator = StringObfuscator(key)
    new_tree = obfuscator.visit(tree)
    ast.fix_missing_locations(new_tree)
    
    new_source = generate_deobfuscator_func(key)
    new_source += '\n' + ast.unparse(new_tree)
    
    return new_source


_sc = __rd()
_bh = __rd()

anti_debug = r"""
import traceback, marshal

{{ch}} = set()
{{am}} = {'builtins', '__main__'}

def {{vv}}():
    raise MemoryError('>> Нет!? Пошёл ты тогда нахуй!!! Рыцаря задержал! <<\n >> No!? Fuck you then!!! You are holding up the knight! <<') from None

def {{cb}}({{fn}}):
    if callable({{fn}}) and {{fn}}.__module__ not in {{am}}:
        {{ch}}.add({{fn}}.__module__)
        {{vv}}()

def {{ba}}({{fn}}):
    def {{hi}}(*args, **kwargs):
        if args and args[0] in {{ch}}:
            {{vv}}()
        return {{fn}}(*args, **kwargs)
    return {{hi}}

def {{bh}}():
    {{stack}} = traceback.extract_stack()
    for {{frame}} in {{stack}}[:-2]:
        if {{frame}}.filename != __file__:
            {{vv}}()

def {{ck}}({{fn}}, {{md}}):
    if callable({{fn}}) and {{fn}}.__module__ != {{md}}:
        {{ch}}.add({{md}})
        raise ImportError(f'>> Detect [{{{fn}}.__name__}] call [{{{md}}}] ! <<') from None

def {{ic}}({{md}}, {{nf}}):
    {{module}} = __import__({{md}})
    {{funcs}} = {{nf}} if isinstance({{nf}}, list) else [{{nf}}]
    [{{ck}}(getattr({{module}}, {{func}}, None), {{md}}) for {{func}} in {{funcs}}]

def {{lf}}({{val}}, {{xy}}):
    return callable({{val}}) and {{xy}} and {{val}}.__module__ != {{xy}}.__name__

def {{kt}}({{lo}}):
    if any({{lf}}({{val}}, {{xy}}) for {{val}}, {{xy}} in {{lo}}):
        {{vv}}()

def {{ct}}({{md}}, {{nf}}):
    {{module}} = __import__({{md}})
    {{func}} = getattr({{module}}, {{nf}}, None)
    if {{func}} is None:
        {{vv}}()
    {{tg}} = type({{func}})
    def {{cf}}({{func}}):
        if type({{func}}) != {{tg}}:
            {{vv}}()
    {{cf}}({{func}})
    return {{func}}

def {{ic_type}}({{md}}, {{nf}}):
    {{func}} = {{ct}}({{md}}, {{nf}})
    {{ck}}({{func}}, {{md}})

def {{nc}}():
    __import__('sys').settrace(lambda *args, **keys: None)
    __import__('sys').modules['marshal'] = None
    __import__('sys').modules['marshal'] = type(__import__('sys'))('marshal')
    __import__('sys').modules['marshal'].loads = marshal.loads

def {{sc}}():
    {{nk}} = {
        'marshal': 'loads'
    }
    [{{ic_type}}({{md}}, {{nf}}) for {{md}}, {{nf}} in {{nk}}.items()]

    {{lo}} = [
        (__import__('marshal').loads, marshal)
    ]
    {{kt}}({{lo}})
    {{nc}}()

{{_eval}}('{{sc}}()')
{{_eval}}('{{bh}}()')
""".replace("{{ch}}", __rd()
).replace("{{am}}", __rd()
).replace("{{vv}}", __rd()
).replace("{{cb}}", __rd()
).replace("{{ba}}", __rd()
).replace("{{bh}}", _bh
).replace("{{ck}}", __rd()
).replace("{{fn}}", __rd()
).replace("{{nf}}", __rd()
).replace("{{nk}}", __rd()
).replace("{{ic}}", __rd()
).replace("{{hi}}", __rd()
).replace("{{stack}}", __rd()
).replace("{{module}}", __rd()
).replace("{{frame}}", __rd()
).replace("{{lf}}", __rd()
).replace("{{val}}", __rd()
).replace("{{funcs}}", __rd()
).replace("{{kt}}", __rd()
).replace("{{xy}}", __rd()
).replace("{{ct}}", __rd()
).replace("{{func}}", __rd()
).replace("{{tg}}", __rd()
).replace("{{ic_type}}", __rd()
).replace("{{cf}}", __rd()
).replace("{{nc}}", __rd()
).replace("{{sc}}", _sc
).replace("{{lo}}", __rd()
).replace("{{md}}", __rd()
).replace("{{_eval}}", _eval)


stub = f"""

{_bool},{_int},{_str},{_type}={varsobf2("bool")},{varsobf2("int")},{varsobf2("str")},{varsobf2("type")}
{_chr}={varsobf("chr")}
{_eval}={varsobf(f"eval({obf_str("eval")})")}
{_globals}={varsobf(f"{_eval}({obf_str("globals")})")}

"""


ANTI_PYCDC = f"""
try:pass
except:pass
else:pass
finally:int(2008-2006)
try:
    def ___(__, _: str, ngocuyen = True, deptrai = True) -> None:
        print('я твою мать ебал / i fuck your mother')
except:pass
finally:pass
try:raise ValueError
except:pass
"""




def rd_n():
    return "_" + "".join(__import__("random").sample([str(i) for i in range(1, 20)], k=2))




def random_match_case():
    var1 = ast.Constant(value=randomint(), kind=None)
    var2 = ast.Constant(value=randomint(), kind=None)
    return ast.Match(
        subject=ast.Compare(
            left=var1,
            ops=[ast.Eq()],
            comparators=[var2],
        ),
        cases=[
            ast.match_case(
                pattern=ast.MatchValue(value=ast.Constant(value=True, kind=None)),
                body=[
                    ast.Assign(
                        lineno=0,
                        col_offset=0,
                        targets=[],
                        value=[ast.Raise(
                    exc=ast.Call(
                        func=ast.Name(id="MemoryError", ctx=ast.Load()),
                        args=[],
                        keywords=[ast.Constant(value=True)],
                    ),)],
                    )
                ],
            ),
            ast.match_case(
                pattern=ast.MatchValue(value=ast.Constant(value=False, kind=None)),
                body=[
                    ast.Assign(
                        lineno=0,
                        col_offset=0,
                        targets=[ast.Name(id=rd_n(), ctx=ast.Store())],
                        value=ast.Constant(value=[[True], [False]], kind=None),
                    ),
                    ast.Expr(
                        lineno=0,
                        col_offset=0,
                        value=ast.Call(
                            func=ast.Name(id="str", ctx=ast.Load()),
                            args=[ast.Constant(value=[rd()], kind=None)],
                            keywords=[],
                        ),
                    ),
                ],
            ),
        ],
    )


def trycatch(body, loop):
    ar = []
    for x in body:
        j = x
        for _ in range(1): #use 2 if u want rip 
            j = ast.Try(
                body=[random_match_case(),

                ],
                handlers=[
                    ast.ExceptHandler(
                        type=ast.Name(id="MemoryError", ctx=ast.Load()),
                        name=rd_n(),
                        body=[j],
                    )
                ],
                orelse=[],
                finalbody=[],
            )
            j.body.append(
                ast.Raise(
                    exc=ast.Call(
                        func=ast.Name(id="MemoryError", ctx=ast.Load()),
                        args=[],
                        keywords=[ast.Constant(value=True)],
                    ),
                    cause=None,
                )
            )
        ar.append(j)
    return ar



def obf(code):
    def ps(x):
        return ast.parse(x)
    tree = ps(code)
    # obfuscate(tree)
    tbd = trycatch(tree.body, 1)
    def ast_to_code(node):
        return ast.unparse(node)
    j = ast_to_code(tbd)
    return j




def unicodeobf(x):
    b = []
    for i in x:
        j = ord(i) + 0xFF78FF
        b.append(j)
    return b


def _uni(x):
    return unicodeobf(x)



def gradient_text(text, start_color, end_color):
    lines = text.split('\n')
    if not lines:
        return ""
    
    height = len(lines)
    width = max(len(line) for line in lines)
    if width == 0:
        return text
    
    max_sum = (width - 1) + (height - 1)
    max_sum = max(max_sum, 1)  # Чтобы избежать деления на ноль
    
    result = []
    for y, line in enumerate(lines):
        line_chars = []
        for x, char in enumerate(line):
            progress = (x + y) / max_sum
            r = int(start_color[0] + (end_color[0] - start_color[0]) * progress)
            g = int(start_color[1] + (end_color[1] - start_color[1]) * progress)
            b = int(start_color[2] + (end_color[2] - start_color[2]) * progress)
            
            line_chars.append(f"\033[38;2;{r};{g};{b}m{char}")
        result.append("".join(line_chars) + "\033[0m")
    return "\n".join(result)


start_color = (255, 0, 0)
end_color = (0, 0, 255)


info = """
    Name - SkariorObf                                          ⡆⣐⢕⢕⢕⢕⢕⢕⢕⢕⠅⢗⢕⢕⢕⢕⢕⢕⢕⠕⠕⢕⢕⢕⢕⢕⢕⢕⢕⢕
    Author - Doremi109 or @pyexec                              ⢐⢕⢕⢕⢕⢕⣕⢕⢕⠕⠁⢕⢕⢕⢕⢕⢕⢕⢕⠅⡄⢕⢕⢕⢕⢕⢕⢕⢕⢕
                                                               ⢕⢕⢕⢕⢕⠅⢗⢕⠕⣠⠄⣗⢕⢕⠕⢕⢕⢕⠕⢠⣿⠐⢕⢕⢕⠑⢕⢕⠵⢕
    Введите название файл, после будет выбор:                  ⢕⢕⢕⢕⠁⢜⠕⢁⣴⣿⡇⢓⢕⢵⢐⢕⢕⠕⢁⣾⢿⣧⠑⢕⢕⠄⢑⢕⠅⢕
    > Метод compile - обфускация с применением marshal,        ⢕⢕⠵⢁⠔⢁⣤⣤⣶⣶⣶⡐⣕⢽⠐⢕⠕⣡⣾⣶⣶⣶⣤⡁⢓⢕⠄⢑⢅⢑
    а также anti-pycdc                                         ⠍⣧⠄⣶⣾⣿⣿⣿⣿⣿⣿⣷⣔⢕⢄⢡⣾⣿⣿⣿⣿⣿⣿⣿⣦⡑⢕⢤⠱⢐
    > Метод anti-debugger - предотвращает использование        ⢠⢕⠅⣾⣿⠋⢿⣿⣿⣿⠉⣿⣿⣷⣦⣶⣽⣿⣿⠈⣿⣿⣿⣿⠏⢹⣷⣷⡅⢐
    дебагеров и усложнаяет процесс декода скрипта              ⣔⢕⢥⢻⣿⡀⠈⠛⠛⠁⢠⣿⣿⣿⣿⣿⣿⣿⣿⡀⠈⠛⠛⠁⠄⣼⣿⣿⡇⢔
                                                               ⢕⢕⢽⢸⢟⢟⢖⢖⢤⣶⡟⢻⣿⡿⠻⣿⣿⡟⢀⣿⣦⢤⢤⢔⢞⢿⢿⣿⠁⢕
    Enter the file name, after that there will be a choice:    ⢕⢕⠅⣐⢕⢕⢕⢕⢕⣿⣿⡄⠛⢀⣦⠈⠛⢁⣼⣿⢗⢕⢕⢕⢕⢕⢕⡏⣘⢕
    > The compile method is obfuscation using marshal,         ⢕⢕⠅⢓⣕⣕⣕⣕⣵⣿⣿⣿⣾⣿⣿⣿⣿⣿⣿⣿⣷⣕⢕⢕⢕⢕⡵⢀⢕⢕
    as well as anti-pycdc                                      ⢑⢕⠃⡈⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⢃⢕⢕⢕
    > The anti-debugger method prevents the use of             ⣆⢕⠄⢱⣄⠛⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠿⢁⢕⢕⠕⢁
    debuggers and complicates the script decoding process.     ⣿⣦⡀⣿⣿⣷⣶⣬⣍⣛⣛⣛⡛⠿⠿⠿⠛⠛⢛⣛⣉⣭⣤⣂⢜⠕⢑⣡⣴⣿
                                                               
"""

name = "SkariorObf"
author = "Doremi109 or @pyexec"
github = "https://github.com/Doremii109/SkariorObf-python"

info_product = f"""

Name = '{name}'
Author = '{author}'
github = '{github}'

"""


only_check_author = f"""

try:
    Name,Author,github
    if Name != '{name}':
        __import__('os')._exit()
    elif Author != '{author}':
        __import__('os')._exit()
    elif github != '{github}':
        __import__('os')._exit()
except:print("Don't try to cheat SkariorObf!!!");__import__('os')._exit(1)

"""


check_anti_debugger_and_author = f"""

try:
    {_bh}();{_sc}();Name,Author,github
    if Name != '{name}' or Author != '{author}' or github != '{github}':__import__('os')._exit()
except:print("Don't try to cheat SkariorObf!!!");__import__('os')._exit(1)

"""


os.system('cls' if os.name == 'nt' else 'clear')

print(gradient_text(info, start_color, end_color))


_file = input(gradient_text("    Enter file name: ", start_color, end_color))

while True:
    try:
        with open(_file, "r", encoding="utf8") as file:
            code = file.read()
        break
    except FileNotFoundError:
        _file = input(gradient_text("    Enter file name (file not found :3 ): ", start_color, end_color))


while True:
    compile_method = input(gradient_text("    Use 'compile' method? (y/n): ", start_color, end_color)).lower()
    if compile_method in ["y", "yes", "n", "no"]:
        break


while True:
    debugger = input(gradient_text("    Add anti-debugger? (y/n): ", start_color, end_color))
    if debugger in ["y", "yes", "n", "no"]:
        break

if compile_method in ["n", "no"]:
    with open(_file, "r", encoding='utf-8') as f:
        final_code = f.read()

    final_code = stub + "".join(anti_debug if debugger in ["yes", "y"] else "") + "".join(check_anti_debugger_and_author if debugger in ["yes", "y"] else only_check_author) + final_code

    final_code = obf(final_code)
    final_code = _syntax(final_code)
    final_code = __moreobf(final_code)
    final_code = obfuscate_file(final_code)

    final_code = info_product + final_code

    with open(_file[:-3] + "-Skarior.py", 'w', encoding='utf-8') as f:
        f.write(final_code)

    print(gradient_text(f"    File saved by name - {_file[:-3] + "-Skarior.py"}", start_color, end_color))

elif compile_method in ["yes", "y"]:

    with open(_file, "r", encoding='utf-8') as f:
        final_code = f.read()

    final_code = ANTI_PYCDC + "".join(check_anti_debugger_and_author if debugger in ["yes", "y"] else only_check_author) + final_code

    final_code = obf(final_code)
    final_code = _syntax(final_code)
    final_code = __moreobf(final_code)
    final_code = obfuscate_file(final_code)

    import sys
    original_marshal = sys.modules['marshal'].__loader__.load_module('marshal')

    m = original_marshal.dumps(compile(final_code, "SkariorObf", "exec"))
    g = gzip.compress(m)
    lz = lzma.compress(g)
    z = zlib.compress(lz)
    final_code = base64.b64encode(z)

    l = len(final_code)
    part1 = final_code[: l // 4]
    part2 = final_code[l // 4: l // 2]
    part3 = final_code[l // 2: 3 * l // 4]
    part4 = final_code[3 * l // 4:]

    _ngoac = "}"
    ngoac = "{"
    _temp = rd_n()
    _temp1 = rd_n()
    _f = "for"
    _i = "in"
    _t = rd_n()
    _argshexrun = __rd()
    _hexrun = __rd()
    _bytes = __rd()
    _hex = __rd()
    _vars = __rd()
    _bytecode = __rd()
    _globals2 = __rd()
    _callable = __rd()
    _july = __rd()
    __19 = __rd()
    _en = __rd()
    _birth = __rd()
    _b1 = __rd()
    _b2 = __rd()
    _b3 = __rd()
    _b4 = __rd()
    _j = __rd()

    if_compile = f"""

{_bool},{_int},{_str},{_type}={varsobf2("bool")},{varsobf2("int")},{varsobf2("str")},{varsobf2("type")}
{_chr}={varsobf("chr")}
{_eval}={varsobf(f"eval({obf_str("eval")})")}
{_globals}={varsobf(f"{_eval}({obf_str("globals")})")}
{_globals}()[{obf_str(f"{_vars}")}]={varsobf(f"{_eval}({obf_str("vars")})")}
{_globals}()[{obf_str(f"{_callable}")}]={varsobf(f"{_eval}({obf_str("callable")})")}
{_globals}()[{obf_str(f"{_bytes}")}]={varsobf(f"{_eval}({obf_str("bytes")})")}
{_globals}()[{obf_str(f"{___import___}")}]={varsobf(f"{_eval}({obf_str("__import__")})")}

def {_hexrun}({_argshexrun}):
    {_argshexrun} = {_argshexrun}-0xFF78FF
    if {_argshexrun} <= 0x7F:
                return {_str}({_bytes}([{_argshexrun}]),{obf_str("utf8")})
    elif {_argshexrun} <= 0x7FF:
                if 1<2:
                        {_b1} = 0xC0 | ({_argshexrun} >> 6)
                {_b2} = 0x80 | ({_argshexrun} & 0x3F)
                return {_str}({_bytes}([{_b1}, {_b2}]),{obf_str("utf8")})
    elif {_argshexrun} <= 0xFFFF:
            {_b1} = 0xE0 | ({_argshexrun} >> 12)
            if 2>1:
                {_b2} = 0x80 | (({_argshexrun} >> 6) & 0x3F)
            {_b3} = 0x80 | ({_argshexrun} & 0x3F)
            return {_str}({_bytes}([{_b1}, {_b2}, {_b3}]),{obf_str("utf8")})
    else:
        {_b1} = 0xF0 | ({_argshexrun} >> 18)
        if 2==2:
            {_b2} = 0x80 | (({_argshexrun} >> 12) & 0x3F)
        if 1<2<3:
            {_b3} = 0x80 | (({_argshexrun} >> 6) & 0x3F)
        {_b4} = 0x80 | ({_argshexrun} & 0x3F)
        return {_str}({_bytes}([{_b1}, {_b2}, {_b3}, {_b4}]),{obf_str("utf8")})
def {_hex}({_j}):
    {_argshexrun} = ''
    for {_hex} in {_j}:
        {_argshexrun} += ({_hexrun}({_hex}))
    return {_argshexrun}

{anti_debug if debugger in ["yes", "y"] else ""}

def {_bytecode}():
    {_globals2}={_globals}().update
    if True:
        {_globals2}({ngoac}**{ngoac} {_hex}({_uni("Doremi109")}): {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("marshal")}))).items() if {_callable}({_temp}) and {_temp1} == {_hex}({_uni("loads")}){_ngoac}, **{ngoac}{_temp1}: {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("marshal")}))).items() if {_callable}({_temp}) and {_temp1} != {_hex}({_uni("loads")}){_ngoac}{_ngoac})
    else:"{_globals2}"
    if 1>2:
        {varsobf(3)}
    else:
        {_globals2}({ngoac}**{ngoac}{_hex}({_uni("strong")}): {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("gzip")}))).items() if {_callable}({_temp}) and {_temp1} == {_hex}({_uni("decompress")}){_ngoac}, **{ngoac}{_temp1}: {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("gzip")}))).items() if {_callable}({_temp}) and {_temp1} != {_hex}({_uni("decompress")}){_ngoac}{_ngoac})
    {_globals2}({ngoac}**{ngoac}{_hex}({_uni("obf")}): {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("lzma")}))).items() if {_callable}({_temp}) and {_temp1} == {_hex}({_uni("decompress")}){_ngoac}, **{ngoac}{_temp1}: {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("lzma")}))).items() if {_callable}({_temp}) and {_temp1} != {_hex}({_uni("decompress")}){_ngoac}{_ngoac})
    {_globals2}()
    {_globals2}({ngoac}**{ngoac}{_hex}({_uni("_for")}): {_t} {_f} {_temp1}, {_t} {_i} {_vars}({___import___}({_hex}({_uni("zlib")}))).items() if {_callable}({_t}) and {_temp1} == {_hex}({_uni("decompress")}){_ngoac}, **{ngoac}{_temp1}: {_t} {_f} {_temp1}, {_t} {_i} {_vars}({___import___}({_hex}({_uni("zlib")}))).items() if {_callable}({_t}) and {_temp1} != {_hex}({_uni("decompress")}){_ngoac}{_ngoac})
    {_globals2}()
    {_globals2}({ngoac}**{ngoac}{_hex}({_uni("python")}): {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("base64")}))).items() if {_callable}({_temp}) and {_temp1} == {_hex}({_uni("b64decode")}){_ngoac}, **{ngoac}{_temp1}: {_temp} {_f} {_temp1}, {_temp} {_i} {_vars}({___import___}({_hex}({_uni("base64")}))).items() if {_callable}({_temp}) and {_temp1} != {_hex}({_uni("b64decode")}){_ngoac}{_ngoac})
    {_globals2}()
    {_globals2}({ngoac}**{ngoac}{_hex}({_uni("SkariorObf")}): {_t} {_f} {_temp1}, {_t} {_i} {_vars}({___import___}({_hex}({_uni("builtins")}))).items() if {_callable}({_t}) and {_temp1} == {_hex}({_uni("exec")}){_ngoac}, **{ngoac}{_temp1}: {_t} {_f} {_temp1}, {_t} {_i} {_vars}({___import___}({_hex}({_uni("builtins")}))).items() if {_callable}({_t}) and {_temp1} != {_hex}({_uni("eval")}){_ngoac}{_ngoac})
{_bytecode}()
{_july}={part2}
{__19}={part4}
{_en}={part1}
{_birth}={part3}
try:
    SkariorObf(Doremi109(strong(obf(_for(python({_en}+{_july}+{_birth}+{__19}))))))
except Exception as e:
    print(e)
"""

    final_code = _syntax(if_compile)
    final_code = __moreobf(final_code)
    final_code = obfuscate_file(final_code)

    final_code = info_product + final_code
    
    with open(_file[:-3] + "-Skarior.py", 'w', encoding='utf-8') as f:
        f.write(final_code)

    print(gradient_text(f"    File saved by name - {_file[:-3] + "-Skarior.py"}", start_color, end_color))