#!/usr/bin/env bash
#
# docker_setup.sh — build the solver into a self-contained, fully static
# x86-64 Linux binary inside a Debian 13.5 container.
#
# HiGHS is baked into the builder image (see ./Dockerfile) as a static library
# at /opt/highs, so you never pass include/lib paths yourself and the resulting
# binary has NO runtime dependencies (not even HiGHS or libstdc++).
#
# Usage:
#   ./docker_setup.sh                       # build submission.cpp -> linux/submission
#   ./docker_setup.sh <source.cpp> [output] # build any HiGHS-based source
#
# Examples:
#   ./docker_setup.sh
#   ./docker_setup.sh submission.cpp my_solver
#
# Requirements on the host: Docker (with buildx; bundled with modern Docker).
#
set -euo pipefail

IMAGE="maf-highs-builder-deb13"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

SRC="${1:-submission.cpp}"
OUT="${2:-}"

# Default: submission.cpp -> linux/submission ; otherwise <basename> next to script.
if [ -z "${OUT}" ]; then
    if [ "${SRC}" = "submission.cpp" ]; then
        OUT="linux/submission"
    else
        OUT="$(basename "${SRC%.*}")"
    fi
fi

if [ ! -f "${HERE}/${SRC}" ]; then
    echo "error: source file '${SRC}' not found in ${HERE}" >&2
    exit 1
fi

mkdir -p "${HERE}/$(dirname "${OUT}")"

# --- Build the builder image once (HiGHS baked in) ------------------------
if ! docker image inspect "${IMAGE}" >/dev/null 2>&1; then
    echo ">> building builder image '${IMAGE}' (one-time; compiles HiGHS)..."
    docker buildx build --platform linux/amd64 -t "${IMAGE}" --load "${HERE}"
fi

# --- Compile (fully static x86-64) ----------------------------------------
echo ">> compiling ${SRC} -> ${OUT} (static x86-64 linux)"
docker run --rm --platform linux/amd64 -v "${HERE}:/work" -w /work "${IMAGE}" \
    g++ -O3 -DNDEBUG -std=c++17 \
        "${SRC}" \
        -I/opt/highs/include \
        -I/opt/highs/include/highs \
        /opt/highs/lib/libhighs.a \
        -static \
        -pthread -ldl -lm \
        -o "${OUT}"

chmod +x "${HERE}/${OUT}"
echo ">> done: ${HERE}/${OUT}"
echo "   Run it with:  ${OUT} --time-limit 300 < instance.txt"
