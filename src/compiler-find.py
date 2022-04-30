import json
import sys

from spack.compilers import find_compilers

# The first argument is the path to the currently executing script.
sys.argv = sys.argv[1:]

# If no arguments are provided, use the paths from config; otherwise, override the paths to check.
paths = sys.argv or None
spec_dicts = [compiler.spec.to_dict() for compiler in find_compilers(paths)]

print(json.dumps(spec_dicts))
