import sys

from spack.compilers import find_compilers

# The first argument is the path to the currently executing script.
sys.argv = sys.argv[1:]

for compiler in find_compilers(sys.argv or None):
    print(compiler.spec)
