/* Minimal stub of common_types.h for the -O0 fixture build (the original
   header is not in the repo; only DestroyFunc/Pointer are used by
   ADTList.h/list.c). */
#pragma once
typedef void (*DestroyFunc)(void*);
typedef void* Pointer;
typedef int (*CompareFunc)(void*, void*);
