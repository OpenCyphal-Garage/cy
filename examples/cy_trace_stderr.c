// Add this file to your build to define cy_trace() that prints trace messages into stderr.

#include "cy_platform.h"
#include <time.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

void cy_trace(cy_t* const         cy,
              const char* const   file,
              const uint_fast16_t line,
              const char* const   func,
              const char* const   format,
              ...)
{
    // Capture the uptime timestamp ASAP.
    const cy_us_t uptime_us = cy_now(cy) - cy->ts_started;

    // Get the current wall time and format it.
    struct timespec ts;
    (void)timespec_get(&ts, TIME_UTC);
    const struct tm tm_local  = *localtime(&ts.tv_sec);
    char            hhmmss[9] = { 0 };
    (void)strftime(hhmmss, sizeof(hhmmss), "%H:%M:%S", &tm_local);

    // Extract the file name.
    const char* file_name = strrchr(file, '/');
    file_name             = (file_name == NULL) ? strrchr(file, '\\') : file_name;
    file_name             = (file_name != NULL) ? (file_name + 1) : file;

    // Update the longest seen file name and function name.
    static _Thread_local int longest_file_name = 15;
    static _Thread_local int longest_func_name = 30;
    const int                file_name_length  = (int)strlen(file_name);
    const int                func_name_length  = (int)strlen(func);
    longest_file_name = (longest_file_name > file_name_length) ? longest_file_name : file_name_length;
    longest_func_name = (longest_func_name > func_name_length) ? longest_func_name : func_name_length;

    // Print the header.
    static const int32_t mega = 1000000;
    (void)fprintf(stderr,
                  "CY(%05lld.%06lld) %s.%03lld %*s:%04u:%*s: ",
                  (long long)(uptime_us / mega),
                  (long long)(uptime_us % mega),
                  hhmmss,
                  (long long)ts.tv_nsec / mega,
                  longest_file_name,
                  file_name,
                  (unsigned)line,
                  longest_func_name,
                  func);

    // Print the message.
    va_list args;
    va_start(args, format);
    (void)vfprintf(stderr, format, args);
    va_end(args);

    // Finalize.
    (void)fputc('\n', stderr);
    (void)fflush(stderr);
}
