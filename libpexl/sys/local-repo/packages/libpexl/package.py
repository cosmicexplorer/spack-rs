# Copyright 2013-2023 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack.package import *

class Libpexl(MakefilePackage):
    """High-performance regular expression matching library."""

    homepage = "https://gitlab.com/pexlang/libpexl"
    git = "https://gitlab.com/pexlang/libpexl.git"

    version("main", branch="main")
    version("arbitrary",
            commit="2dfd9530032c8caf28976cced14011752e24c2ba")

    license("BSD-3-Clause")

    def build(self, spec, prefix):
        make("-C", "src", "AR=ar", "RANLIB=ranlib")

    def install(self, spec, prefix):
        mkdirp(prefix.include)
        mkdirp(prefix.lib)
        make(f"DESTDIR={prefix}", "-C", "src", "install")
