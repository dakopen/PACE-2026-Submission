# PACE 2026 — Maximum Agreement Forest solver

An heuristic solver for the **Maximum Agreement Forest** problem (PACE 2026
heuristic track). It reads a problem instance on **stdin** and writes the agreement
forest to **stdout**.

## Contents

```
PACE-2026-Submission/
├── INSTALL.md          # this file
├── Dockerfile          # Debian 13.5 builder image with HiGHS baked in (static)
├── docker_setup.sh     # one-shot reproducible build in a Debian 13.5 container
├── submission.cpp      # the complete solver (single translation unit)
├── linux/submission    # prebuilt x86-64 Linux binary — fully STATIC, no runtime deps
└── macos/submission    # prebuilt arm64 macOS binary (needs Homebrew HiGHS at runtime)
```

The prebuilt **Linux** binary is **fully statically linked** (HiGHS, libstdc++
and glibc are baked in) — it runs on any x86-64 Linux with no dependencies at all,
not even HiGHS. The prebuilt **macOS** binary is dynamically linked and needs
Homebrew's HiGHS installed to run. Either way, the reliable path is to rebuild
from `submission.cpp` (see below).

## External dependencies

| Dependency | Version used | Purpose |
|------------|--------------|---------|
| A C++17 compiler (`g++` or `clang++`) | any recent | compile `submission.cpp` |
| **HiGHS** (LP/MIP solver) | **1.15.1**, built from source (see `Dockerfile`); macOS build used Homebrew 1.15 | linear-programming master in column generation |
| POSIX threads (`-pthread`) | — | HiGHS internal parallelism |

There are **no other dependencies** and **no environment variables** are read by
the solver. All behaviour is controlled through command-line flags.

## Build

### Recommended: Debian 13.5 container (fully static binary)

This is the reproducible build the grader can run as-is. It builds a Debian 13.5
image with HiGHS 1.15.1 compiled as a static library (`Dockerfile`), then links
`submission.cpp` into a single self-contained x86-64 binary:

```sh
./docker_setup.sh          # -> linux/submission  (static x86-64, no runtime deps)
```

Requires only Docker on the host. The first run compiles HiGHS (a few minutes,
cached thereafter). To pin a different HiGHS release, edit `HIGHS_VERSION` in the
`Dockerfile` and remove the `maf-highs-builder-deb13` image so it rebuilds.

### Debian / Ubuntu (Linux), dynamic link against the system HiGHS

If you prefer to link against the distro's HiGHS instead of building it from
source (Debian 13 ships HiGHS 1.10.0), the binary will be dynamically linked and
needs `libhighs` present at runtime:

```sh
sudo apt-get update
sudo apt-get install -y g++ libhighs-dev
g++ -O3 -DNDEBUG -std=c++17 submission.cpp \
    -I/usr/include/highs \
    -lhighs -pthread -o submission
```

`-I/usr/include/highs` is required because the packaged HiGHS headers use include
paths relative to that directory.

### macOS (Homebrew)

```sh
brew install highs
g++ -O3 -DNDEBUG -std=c++17 submission.cpp \
    -I/opt/homebrew/include -I/opt/homebrew/include/highs \
    -L/opt/homebrew/lib \
    -lhighs -pthread -o submission
```

## Running

The solver reads an instance from stdin and writes the forest to stdout:

```sh
./submission --time-limit 300 < instance.txt > solution.txt
```

### Command-line options

| Flag | Default | Meaning |
|------|---------|---------|
| `--time-limit S` | `300` | Wall-clock budget in seconds. **Set this to your evaluation budget.** |
| `--disable-kernel` | off | Skip the kernelization / reduction phase |
| `--quiet` | off | Suppress progress logging on stderr |
| `-h`, `--help` | — | Print usage |

> ### ⚠️ Important: pass `--time-limit` to match your budget
>
> This solver reads **no environment variables** — in particular it does **not**
> read `STRIDE_TIMEOUT`. Under the STRIDE harness the per-instance budget is
> delivered through that environment variable, which this solver ignores.
>
> If you do not pass `--time-limit`, the solver plans against its internal default
> of **300 seconds**. It is fully anytime — it continuously publishes its best
> forest and, on `SIGTERM`, immediately prints the best solution found — so it
> still returns a valid answer when killed early. But for the solver to schedule
> its phases correctly it must know the real budget. **Always pass
> `--time-limit S` equal to the STRIDE soft timeout**, e.g. under STRIDE:
>
> ```sh
> stride run -i <list> -s ./submission -t 300 -- --time-limit 300
> ```
>
> The arguments after `--` are forwarded verbatim to the solver.

## Output format

The first line is `# tree size K` (number of components), followed by `K` lines,
each a Newick tree (or a bare leaf label) terminated by `;`. The forest is a
partition of the leaf set that is an agreement forest of the input trees.
