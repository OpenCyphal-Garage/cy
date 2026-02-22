# Cy development guidelines for AI agents

Read `README.md` for general information about the project, as well as all READMEs in subdirectories except `lib/` if you see any.

The library sources are under the `cy/` directory; everything else is ancillary. The `lib/` directory contains dependencies and generally there is no need to look there.

The library code must be fully portable between different architectures and compilers, from baremetal to POSIX, from 8-bit to 64-bit.

You must read all files in their entirety instead of using search tools for best context awareness.

Update docs/examples when public API behavior changes.

## Project Structure & Module Organization

- `cy/`: the library itself, which is transport-agnostic and platform-agnostic.
- `tests/`: the test suite; refer to its own README.
- `examples/`: runnable demos.
- `lib/`: all external dependencies for the library itself, for the test suite, and for the demos.
- `formal_verification/`: formal verification models.

## Coding Style & Naming Conventions

- Language targets: C99+ for Cy, C11 and C++20 for the test harness. Strict std only, compiler extensions not allowed.
- Naming patterns: `cy_*` functions, `cy_*_t` types, `CY_*` macros. Internal definitions need no prefixing. Enums and constants are `lower_snake_case`. Uppercase only for macros.
- Keep code compact and add brief comments before non-obvious logic.
- Treat warnings as errors and keep compatibility with strict warning flags.
- Module entities are prefixed with the module name; e.g., `foo.h` contains `foo_bar`, `foo_baz_t`, `FOO_QUX`. Module-local statics must not be prefixed to keep things brief.
