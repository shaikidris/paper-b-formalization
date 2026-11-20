import concurrent.futures
from pathlib import Path
import re
import subprocess
import sys

ir = Path(sys.argv[1]).resolve()
toolchain = Path(sys.argv[2]).resolve()
here = Path(__file__).resolve().parent
output = Path(sys.argv[3]).resolve()
output.mkdir(parents=True, exist_ok=True)
objects = output / "objects"
objects.mkdir(exist_ok=True)
clang = ("clang", "-I", str(toolchain / "include"), "-O1", "-DNDEBUG", "-w")
todo = ["PaperB_ForestOrderRank"]
sources = {}
while todo:
    name = todo.pop()
    if name in sources:
        continue
    path = ir / (name.replace("_", "/") + ".c")
    if not path.is_file():
        raise FileNotFoundError(path)
    sources[name] = path
    todo.extend(set(re.findall(r"initialize_paperB_([A-Za-z0-9_]+)\(", path.read_text())))
print(f"Compiling {len(sources)} modules", flush=True)

def compile_one(item):
    name, path = item
    target = objects / (name + ".o")
    body = path.read_text()
    # Rewrite emitted call expressions and leave function declarations alone.
    body = re.sub(
        r"(= |return )(lean_array_(?:fset|set|uset|push))\(([^;\n]+)\);",
        lambda m: f'{m[1]}audit_{m[2][11:]}({m[3]},__FILE__,__LINE__);',
        body)
    declarations = (here / "audit.h").read_text().split("#define",1)[0]
    body = declarations + f'\n#line 1 "{path.name}"\n' + body
    subprocess.run((*clang,"-x","c","-c","-o",str(target),"-"),
                   input=body.encode(),check=True)
    return target

with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
    linked = list(pool.map(compile_one, sources.items()))
subprocess.run((*clang,"-c",str(here/"audit.c"),"-o",str(objects/"audit.o")),check=True)
subprocess.run((str(toolchain/"bin/leanc"),"-o",str(output/"audit"),
                str(objects/"audit.o"),*map(str,linked)),check=True)
