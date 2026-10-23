"""Hand-written facts about glibc functions that its headers do not state.

The generator takes types, parameter constness, `const`/`pure`/`noreturn`
attributes and variadic-ness from the headers; everything here is what a
reader of the C library's documentation knows and a prototype does not.
Each table is a claim about the library, so keep an entry only when the
documented behaviour guarantees it.
"""

# Functions that never return to their caller, beyond the ones the
# headers mark `noreturn`.  (`exit` and friends are marked; these are not.)
NORETURN = {
    "__stack_chk_fail", "__chk_fail", "__fortify_fail", "__assert_fail",
    "__assert_perror_fail", "__assert", "_Exit", "_exit", "abort", "exit",
    "quick_exit", "pthread_exit", "longjmp", "siglongjmp", "_longjmp",
    "__longjmp_chk", "__libc_fatal", "thrd_exit", "__cxa_throw",
    "__cxa_rethrow", "__cxa_bad_cast", "__cxa_bad_typeid",
    "__cxa_call_unexpected", "__libc_start_main", "execl", "execle",
    "execlp", "execv", "execve", "execvp", "execvpe", "fexecve",
}

# Pointer parameters of these functions are used for the duration of the
# call only: the callee does not keep the pointer, so a stack address
# passed here does not outlive the call.  Names, not headers: a retainer
# (atexit, putenv, setvbuf, getopt, tsearch ...) is simply absent.
NONCAPTURING = set("""
memcpy memmove memset memcmp memchr memrchr rawmemchr mempcpy memccpy bcmp
bcopy bzero explicit_bzero timingsafe_bcmp
strlen strnlen strcpy strncpy strcat strncat strcmp strncmp strcasecmp
strncasecmp strchr strrchr strchrnul strstr strcasestr strspn strcspn
strpbrk stpcpy stpncpy strcoll strxfrm strdup strndup strverscmp strfry
strsep memfrob index rindex ffs
wcslen wcscpy wcsncpy wcscat wcsncat wcscmp wcsncmp wcschr wcsrchr wcsstr
wcsspn wcscspn wcspbrk wmemcpy wmemmove wmemset wmemcmp wmemchr wcscoll
wcsxfrm wcsdup wcstol wcstoul wcstoll wcstoull wcstod wcstof wcstold
printf fprintf dprintf sprintf snprintf asprintf vprintf vfprintf vdprintf
vsprintf vsnprintf vasprintf __printf_chk __fprintf_chk __dprintf_chk
__sprintf_chk __snprintf_chk __vprintf_chk __vfprintf_chk __vdprintf_chk
__vsprintf_chk __vsnprintf_chk __asprintf_chk __vasprintf_chk
scanf fscanf sscanf vscanf vfscanf vsscanf __isoc99_scanf __isoc99_fscanf
__isoc99_sscanf __isoc99_vscanf __isoc99_vfscanf __isoc99_vsscanf
__isoc23_scanf __isoc23_fscanf __isoc23_sscanf __isoc23_vscanf
__isoc23_vfscanf __isoc23_vsscanf
fopen fopen64 freopen freopen64 fdopen fclose fflush fgets fgets_unlocked
fputs fputs_unlocked puts fputc fputc_unlocked putc putc_unlocked putchar
fgetc getc getchar fread fwrite fread_unlocked fwrite_unlocked fseek fseeko
fseeko64 ftell ftello ftello64 rewind fgetpos fsetpos fgetpos64 fsetpos64
feof ferror clearerr fileno getline getdelim perror remove rename tmpfile
ungetc fprintf_unlocked flockfile funlockfile ftrylockfile
__fgets_chk __fread_chk __fgets_unlocked_chk __fread_unlocked_chk
atoi atol atoll atof strtol strtoul strtoll strtoull strtod strtof strtold
qsort bsearch abs labs llabs div ldiv lldiv getenv secure_getenv malloc free
calloc mkstemp mkostemp mkdtemp realpath system mblen mbtowc wctomb mbstowcs
wcstombs rand srand rand_r random srandom drand48 lrand48 mrand48 erand48
nrand48 jrand48 srand48 seed48 lcong48
read write pread pwrite pread64 pwrite64 close lseek lseek64 access eaccess
euidaccess faccessat unlink unlinkat rmdir chdir fchdir getcwd readlink
readlinkat pipe pipe2 dup dup2 dup3 isatty ttyname ttyname_r link linkat
symlink symlinkat truncate ftruncate truncate64 ftruncate64 fsync fdatasync
sleep usleep alarm getpid getppid getuid geteuid getgid getegid chown
fchown lchown fchownat gethostname sysconf pathconf fpathconf confstr
__read_chk __pread_chk __readlink_chk __getcwd_chk __pread64_chk
__readlinkat_chk
stat fstat lstat fstatat stat64 fstat64 lstat64 fstatat64 mkdir mkdirat chmod
fchmod fchmodat umask mkfifo mknod utimensat futimens statx
open open64 openat openat64 creat creat64 fcntl fcntl64 posix_fadvise
posix_fallocate flock
time clock difftime mktime timegm localtime localtime_r gmtime gmtime_r
ctime ctime_r asctime asctime_r strftime strptime clock_gettime
clock_settime clock_getres nanosleep gettimeofday settimeofday utime utimes
futimes
opendir fdopendir readdir readdir64 readdir_r closedir rewinddir telldir
seekdir dirfd scandir scandir64 alphasort versionsort
wait waitpid waitid wait3 wait4
sigemptyset sigfillset sigaddset sigdelset sigismember sigprocmask
sigpending sigsuspend sigaction kill raise
getrlimit setrlimit getrlimit64 setrlimit64 getrusage getpriority
setpriority
fnmatch glob glob64 globfree regcomp regexec regerror regfree
setlocale localeconv nl_langinfo
iswalpha iswdigit iswspace towlower towupper wctype iswctype
isalnum isalpha isblank iscntrl isdigit isgraph islower isprint ispunct
isspace isupper isxdigit tolower toupper
sin cos tan asin acos atan atan2 sinh cosh tanh exp log log10 log2 pow sqrt
cbrt hypot ceil floor round trunc fabs fmod fmin fmax frexp ldexp modf
scalbn nearbyint rint lrint llrint lround llround copysign nan
sinf cosf tanf expf logf powf sqrtf ceilf floorf roundf truncf fabsf fmodf
""".split())

# Functions that return one of their pointer parameters, by index.
RETURNED = {
    "memcpy": 0, "memmove": 0, "memset": 0, "strcpy": 0, "strncpy": 0,
    "strcat": 0, "strncat": 0, "wcscpy": 0, "wcsncpy": 0, "wcscat": 0,
    "wcsncat": 0, "wmemcpy": 0, "wmemmove": 0, "wmemset": 0, "bcopy": None,
    "__memcpy_chk": 0, "__memmove_chk": 0, "__memset_chk": 0,
    "__strcpy_chk": 0, "__strncpy_chk": 0, "__strcat_chk": 0,
    "__strncat_chk": 0,
}

# Functions that read and write only the memory their pointer parameters
# name (and nothing else visible to the caller): the C string and memory
# functions.  Functions that use a locale, a static buffer or the heap are
# not here.
ARGMEM = set("""
memcpy memmove memset memcmp memchr memrchr rawmemchr mempcpy memccpy bcmp
bcopy bzero explicit_bzero
strlen strnlen strcpy strncpy strcat strncat strcmp strncmp strchr strrchr
strchrnul strstr strspn strcspn strpbrk stpcpy stpncpy strverscmp
wcslen wcscpy wcsncpy wcscat wcsncat wcscmp wcsncmp wcschr wcsrchr wcsstr
wcsspn wcscspn wcspbrk wmemcpy wmemmove wmemset wmemcmp wmemchr
__memcpy_chk __memmove_chk __memset_chk __strcpy_chk __strncpy_chk
__strcat_chk __strncat_chk
""".split())

# The by-value structures the C library's prototypes name.
AGGREGATES = {
    "div_t": "(Aggregate ((size 8) (align 4) (fields (((offset 0) (ty Int)) "
             "((offset 4) (ty Int))))))",
    "ldiv_t": "(Aggregate ((size 16) (align 8) (fields (((offset 0) (ty Long)) "
              "((offset 8) (ty Long))))))",
    "lldiv_t": "(Aggregate ((size 16) (align 8) (fields (((offset 0) (ty Long_long)) "
               "((offset 8) (ty Long_long))))))",
    "imaxdiv_t": "(Aggregate ((size 16) (align 8) (fields (((offset 0) (ty Long)) "
                 "((offset 8) (ty Long))))))",
    "struct in_addr": "(Aggregate ((size 4) (align 4) (fields (((offset 0) (ty Int))))))",
    "ENTRY": "(Aggregate ((size 16) (align 8) (fields (((offset 0) (ty Pointer)) "
             "((offset 8) (ty Pointer))))))",
    "union sigval": "(Aggregate ((size 8) (align 8) (fields (((offset 0) (ty Int)) "
                    "((offset 0) (ty Pointer))))))",
    "sigval_t": "(Aggregate ((size 8) (align 8) (fields (((offset 0) (ty Int)) "
                "((offset 0) (ty Pointer))))))",
    "struct mallinfo": "(Aggregate ((size 40) (align 4) (fields (%s))))" % " ".join(
        "((offset %d) (ty Int))" % (4 * i) for i in range(10)),
    "struct mallinfo2": "(Aggregate ((size 80) (align 8) (fields (%s))))" % " ".join(
        "((offset %d) (ty Long))" % (8 * i) for i in range(10)),
    "cookie_io_functions_t": "(Aggregate ((size 32) (align 8) (fields (%s))))" % " ".join(
        "((offset %d) (ty Pointer))" % (8 * i) for i in range(4)),
    # Transparent unions of pointers: passed as the pointer.
    "__SOCKADDR_ARG": "Pointer",
    "__CONST_SOCKADDR_ARG": "Pointer",
    "__SOCKADDR_ARG_NONNULL": "Pointer",
    "__CONST_SOCKADDR_ARG_NONNULL": "Pointer",
}

# Old libraries whose symbols moved into libc: a binary built against them
# names them in its version requirements.
MOVED = [
    ("libpthread.so.0", ("pthread_", "sem_", "thrd_", "mtx_", "cnd_", "tss_",
                         "call_once", "__pthread", "pthread")),
    ("libdl.so.2", ("dl", "_dl")),
    ("librt.so.1", ("shm_", "mq_", "timer_", "aio_", "lio_", "clock_")),
    ("libutil.so.1", ("openpty", "forkpty", "login", "logout", "logwtmp")),
]

# Prototypes of symbols the compiler and the C library's own headers use
# but no public header declares, as C function types.
EXTRA = {
    "__libc_start_main": "int (void *, int, void *, void *, void *, void *, void *)",
    "__stack_chk_fail": "void (void)",
    "__cxa_atexit": "int (void *, void *, void *)",
    "__cxa_finalize": "void (void *)",
    "__assert_fail": "void (const char *, const char *, unsigned int, const char *)",
    "__errno_location": "int *(void)",
    "__ctype_b_loc": "const unsigned short **(void)",
    "__ctype_tolower_loc": "const int **(void)",
    "__ctype_toupper_loc": "const int **(void)",
    "__printf_chk": "int (int, const char *, ...)",
    "__fprintf_chk": "int (void *, int, const char *, ...)",
    "__sprintf_chk": "int (char *, int, unsigned long, const char *, ...)",
    "__snprintf_chk": "int (char *, unsigned long, int, unsigned long, const char *, ...)",
    "__asprintf_chk": "int (char **, int, const char *, ...)",
    "__dprintf_chk": "int (int, int, const char *, ...)",
    "__vprintf_chk": "int (int, const char *, void *)",
    "__vfprintf_chk": "int (void *, int, const char *, void *)",
    "__vsprintf_chk": "int (char *, int, unsigned long, const char *, void *)",
    "__vsnprintf_chk": "int (char *, unsigned long, int, unsigned long, const char *, void *)",
    "__vasprintf_chk": "int (char **, int, const char *, void *)",
    "__vdprintf_chk": "int (int, int, const char *, void *)",
    "__memcpy_chk": "void *(void *, const void *, unsigned long, unsigned long)",
    "__memmove_chk": "void *(void *, const void *, unsigned long, unsigned long)",
    "__mempcpy_chk": "void *(void *, const void *, unsigned long, unsigned long)",
    "__memset_chk": "void *(void *, int, unsigned long, unsigned long)",
    "__strcpy_chk": "char *(char *, const char *, unsigned long)",
    "__stpcpy_chk": "char *(char *, const char *, unsigned long)",
    "__strncpy_chk": "char *(char *, const char *, unsigned long, unsigned long)",
    "__strcat_chk": "char *(char *, const char *, unsigned long)",
    "__strncat_chk": "char *(char *, const char *, unsigned long, unsigned long)",
    "__fgets_chk": "char *(char *, unsigned long, int, void *)",
    "__fread_chk": "unsigned long (void *, unsigned long, unsigned long, unsigned long, void *)",
    "__read_chk": "long (int, void *, unsigned long, unsigned long)",
    "__pread_chk": "long (int, void *, unsigned long, long, unsigned long)",
    "__readlink_chk": "long (const char *, char *, unsigned long, unsigned long)",
    "__getcwd_chk": "char *(char *, unsigned long, unsigned long)",
    "__realpath_chk": "char *(const char *, char *, unsigned long)",
    "__longjmp_chk": "void (void *, int)",
    "__fdelt_chk": "long (long)",
    "__explicit_bzero_chk": "void (void *, unsigned long, unsigned long)",
}
NONCAPTURING |= {n for n in EXTRA
                 if n not in ("__cxa_atexit", "__libc_start_main")}
