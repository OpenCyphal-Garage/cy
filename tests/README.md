# Cy test suite

The test suite is the primary development environment for Cy. It is composed of two parts: intrusive tests in C that directly `#include <cy.c>` to reach and test the internals, and API-level tests in modern C++ that use the public API only and test the library as a black box. It is preferable to test all behaviors through the API only, and resort to intrusive tests *only when necessary* to reach internal logic that cannot be tested through the API.

If you need a build directory, create one in the project root named with a `build` prefix; you can also use existing build directories if you prefer so, but avoid using `cmake-build-*` because these are used by CLion. Do not create build directories anywhere else.

Clang-Tidy must be enabled during build on all targets except external dependencies (e.g., the test framework). In particular, Clang-Tidy MUST BE ENABLED on the test suite and the Cy library itself at all times.

When compiling, use multiple jobs to use all CPU cores.

Run all tests in debug build to ensure that all assertion checks are enabled. Coverage builds should disable assertion checks to avoid reporting of uncovered fault branches in `assert()` statements.

Use Clang-Format to format the code when done editing.

Refer to the CI workflow files and `CMakeLists.txt` for the recommended practices on how to build and run the test suite.

For coverage measurement:

```bash
cmake -B build -DCOVERAGE=ON -DNO_STATIC_ANALYSIS=ON
cmake --build build
ctest --test-dir build
cmake --build build --target coverage
xdg-open build/coverage/index.html
```
