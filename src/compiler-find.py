import json
import sys

from spack.compilers.config import all_compilers, find_compilers

# The first argument is the path to the currently executing script.
paths = sys.argv[1:]

# If no arguments are provided, use the paths from config; otherwise, override the paths to check.
if paths:
    new_specs = find_compilers(paths)
    print('new specs:', file=sys.stderr)
    print(new_specs, file=sys.stderr)

spec_dicts = [spec.to_dict() for spec in all_compilers()]

print(json.dumps(spec_dicts))
