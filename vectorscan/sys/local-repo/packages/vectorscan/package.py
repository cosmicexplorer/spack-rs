# Copyright 2013-2023 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack.package import *

class Vectorscan(CMakePackage):
    """High-performance regular expression matching library."""

    homepage = "https://www.vectorcamp.gr/vectorscan/"
    url = "https://github.com/VectorCamp/vectorscan/archive/refs/tags/vectorscan/5.4.11.tar.gz"
    git = "https://github.com/VectorCamp/vectorscan.git"
    list_url = "https://github.com/VectorCamp/vectorscan/releases"

    version("v5.4.11", tag="vectorscan/5.4.11")

    license("BSD-3-Clause")

    depends_on("boost+exception+serialization+random+graph+container")
    depends_on("pcre@8.41+utf", when="+chimera")
    depends_on("ragel", type="build")

    variant("chimera", default=False, description="Build the chimera PCRE compat library.")
    variant("shared", default=False, description="Build shared libs")
    variant("static", default=True, description="Build static libs")
    conflicts("~shared~static", msg="must build shared and/or static libs!")
    conflicts("+chimera+shared", msg="chimera does not allow shared libs!")

    # TODO: FAT_RUNTIME flag!

    patch("native-stream-api-5.patch")

    def cmake_args(self):
        args = []
        if '+chimera' in self.spec:
            pcre_stage = self.spec['pcre'].package.stage[0]
            pcre_stage.create()
            pcre_stage.fetch()
            pcre_stage.expand_archive()
            args.extend([
                self.define("PCRE_SOURCE", pcre_stage.source_path),
                self.define("BUILD_CHIMERA", "TRUE"),
            ])

        if '+shared' in self.spec:
            args.append(self.define("BUILD_SHARED_LIBS", "ON"))
        if '+static' in self.spec:
            args.append(self.define("BUILD_STATIC_LIBS", "ON"))

        args.append(self.define("USE_CPU_NATIVE", "ON"))

        features = self.spec.architecture.target.microarchitecture.features
        if 'avx2' in features:
            args.append(self.define("BUILD_AVX2", "ON"))
        if 'avx512' in features:
            args.append(self.define("BUILD_AVX512", "ON"))
        if 'avx512vbmi' in features:
            args.append(self.define("BUILD_AVX512VBMI", "ON"))

        return args
