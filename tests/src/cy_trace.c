#include "cy_platform.h"
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

void cy_trace(cy_t* const         cy, // cppcheck-suppress constParameterPointer
              const char* const   file,
              const uint_fast16_t line,
              const char* const   func,
              const char* const   format,
              ...)
{
    const cy_us_t now = cy_now(cy);

    // Extract the file name.
    const char* file_name = strrchr(file, '/');
    file_name             = (file_name == NULL) ? strrchr(file, '\\') : file_name;
    file_name             = (file_name != NULL) ? (file_name + 1) : file;

    // Print the header.
    static const int32_t mega = 1000000;
    static const int32_t kilo = 1000;
    (void)fprintf(stderr, //
                  "CY_TRACE(%p) %06jd.%03jd %s:%04ju:%s: ",
                  (void*)cy,
                  (intmax_t)(now / mega),
                  (intmax_t)((now % mega) / kilo),
                  file_name,
                  (uintmax_t)line,
                  func);

    // Print the message.
    va_list args; // NOLINT(*-init-variables)
    va_start(args, format);
    (void)vfprintf(stderr, format, args);
    va_end(args);

    // Finalize.
    (void)fputc('\n', stderr);
    (void)fflush(stderr);
}
