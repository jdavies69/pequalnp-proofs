"""Compile the same Lean declarations in smaller modules to bound peak memory."""
import os
from pathlib import Path
import re
import subprocess
import sys

def check(src, dest, name):
    raw = (src / (name + '.lean')).read_text()
    prefix, body = raw.split('theorem ', 1)
    blocks = re.split(r'(?m)^theorem ', 'theorem ' + body)[1:]
    assert len(blocks) >= 2 and blocks[-1].startswith('checkedSegment')
    stage = dest / '.split-src'
    stage.mkdir(exist_ok=True)
    imports = []
    def compile_module(module, contents):
        source = stage / (module + '.lean')
        obj = dest / (module + '.olean')
        if not source.exists() or source.read_text() != contents:
            source.write_text(contents)
        deps = [source, dest / 'DeskForestData.olean']
        if module == name:
            deps.extend(dest / (leaf + '.olean') for leaf in imports)
        if obj.is_file() and obj.stat().st_mtime > max(d.stat().st_mtime for d in deps):
            return
        subprocess.run(['lean', '-j1', '-DElab.async=false', '-R', str(stage),
                        '-o', str(obj), str(source)], check=True)
    for block in blocks[:-1]:
        theorem = block.split(' ', 1)[0]
        assert re.fullmatch(r'B\d+_\d+', theorem)
        leaf = 'Leaf' + theorem
        compile_module(leaf, prefix + 'theorem ' + block + 'end PetersenCertificate\n')
        imports.append(leaf)
    compile_module(name, ''.join('import ' + x + '\n' for x in imports) + prefix +
                   'theorem ' + blocks[-1])
if __name__ == '__main__':
    check(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve(), sys.argv[3])
