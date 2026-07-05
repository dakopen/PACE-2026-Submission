# Builder image for the PACE 2026 MAF solver.
#
# Debian 13.5 (trixie) with the C++ toolchain and HiGHS baked in as a STATIC
# library at /opt/highs, so the solver can be linked into a single self-contained
# x86-64 binary with no runtime dependencies.
#
# Debian's own libhighs-dev ships only a shared object, so HiGHS is built from
# source here (pinned to a fixed release for reproducibility).
FROM debian:13.5

ARG HIGHS_VERSION=v1.15.1
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        g++ cmake make git ca-certificates libc6-dev && \
    rm -rf /var/lib/apt/lists/*

# Build HiGHS as a static library and install it to /opt/highs.
RUN git clone --depth 1 --branch "${HIGHS_VERSION}" \
        https://github.com/ERGO-Code/HiGHS.git /tmp/HiGHS && \
    cmake -S /tmp/HiGHS -B /tmp/HiGHS/build \
        -DCMAKE_BUILD_TYPE=Release \
        -DBUILD_SHARED_LIBS=OFF \
        -DBUILD_TESTING=OFF \
        -DCMAKE_INSTALL_PREFIX=/opt/highs && \
    cmake --build /tmp/HiGHS/build --target install -j"$(nproc)" && \
    rm -rf /tmp/HiGHS

WORKDIR /work
