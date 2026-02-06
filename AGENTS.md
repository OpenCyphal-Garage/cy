# Cy development guidelines for AI agents

Read `README.md` for general information about the project.

The library code must be fully portable between different architectures and compilers, from baremetal to POSIX, from 8-bit to 64-bit.

You must read all files in their entirety instead of using search tools for best context awareness.

Update docs/examples when public API behavior changes.

## Project Structure & Module Organization

- `cy/`: the library itself, which is transport-agnostic and platform-agnostic.
- `cy_udp_posix/`: POSIX/BSD-socket glue layer built on LibUDPard.
- `examples/`: runnable demos.
- `lib/`: single-header dependencies plus the `lib/libudpard` git submodule.
- `formal_verification/`: TLA+ models and helper scripts.
- `dsdl/`: core Cyphal DSDL definitions.

## Build, Test, and Development Commands

If you need a build directory, create one in the project root named with a `build` prefix; you can also use existing build directories if you prefer so, but avoid using `cmake-build-*` because these are used by CLion.

Clang-Tidy must be enabled during build on all targets except external dependencies (e.g., the test framework). In particular, Clang-Tidy MUST BE ENABLED on the test suite and the Cy library itself.

When compiling, use multiple jobs to use all CPU cores.

Run all tests in debug build to ensure that all assertion checks are enabled.

It is best to use Clang-Format to format the code when done editing.

```sh
git submodule update --init --recursive
cmake -S . -B build-debug -DCMAKE_BUILD_TYPE=Debug
cmake --build build-debug -j"$(nproc)"
cmake --build build-debug --target format
```

## Coding Style & Naming Conventions

- Language targets: C99+ for Cy, C11 and C++20 for the test harness. Strict std only, compiler extensions not allowed.
- Naming patterns: `cy_*` functions, `cy_*_t` types, `CY_*` macros. Internal definitions need no prefixing.
- Keep code compact and add brief comments before non-obvious logic.
- Treat warnings as errors and keep compatibility with strict warning flags.
