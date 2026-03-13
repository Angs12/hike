; Function Attrs: nounwind
declare ptr addrspace(0) @tmpnam(ptr addrspace(0) noundef) #1

declare noalias ptr addrspace(0) @tmpfile() #2

; Function Attrs: nounwind
declare i32 @setvbuf(ptr addrspace(0) noundef, ptr addrspace(0) noundef, i32 noundef, i64 noundef) #1

; Function Attrs: nounwind
declare void @setbuf(ptr addrspace(0) noundef, ptr addrspace(0) noundef) #1

declare i32 @fputc(i32 noundef, ptr addrspace(0) noundef) #2

declare i32 @putc(i32 noundef, ptr addrspace(0) noundef) #2

declare i32 @fputs(ptr addrspace(0) noundef, ptr addrspace(0) noundef) #2

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr addrspace(0) noalias writeonly captures(none), ptr addrspace(0) noalias readonly captures(none), i64, i1 immarg) #3

declare i64 @fwrite(ptr addrspace(0) noundef, i64 noundef, i64 noundef, ptr addrspace(0) noundef) #2

declare i32 @fflush(ptr addrspace(0) noundef) #2

declare i32 @fgetpos(ptr addrspace(0) noundef, ptr addrspace(0) noundef) #2

declare i64 @ftell(ptr addrspace(0) noundef) #2

declare void @rewind(ptr addrspace(0) noundef) #2

declare i32 @fseek(ptr addrspace(0) noundef, i64 noundef, i32 noundef) #2

declare i32 @fsetpos(ptr addrspace(0) noundef, ptr addrspace(0) noundef) #2

declare i32 @fgetc(ptr addrspace(0) noundef) #2

declare i32 @getc(ptr addrspace(0) noundef) #2

declare i32 @ungetc(i32 noundef, ptr addrspace(0) noundef) #2

declare ptr addrspace(0) @fgets(ptr addrspace(0) noundef, i32 noundef, ptr addrspace(0) noundef) #2

declare i64 @fread(ptr addrspace(0) noundef, i64 noundef, i64 noundef, ptr addrspace(0) noundef) #2

; Function Attrs: nounwind
declare i32 @feof(ptr addrspace(0) noundef) #1

; Function Attrs: nounwind
declare void @clearerr(ptr addrspace(0) noundef) #1

; Function Attrs: nounwind
declare i32 @ferror(ptr addrspace(0) noundef) #1

declare i32 @putchar(i32 noundef) #2

declare ptr addrspace(1) @malloc(i64 noundef) #2

declare void @free(ptr addrspace(1) noundef) #2

declare i32 @puts(ptr addrspace(0) noundef) #2

declare noalias ptr addrspace(0) @fopen(ptr addrspace(0) noundef, ptr addrspace(0) noundef) #2

; Function Attrs: cold
declare void @perror(ptr addrspace(0) noundef) #4

declare ptr addrspace(0) @freopen(ptr addrspace(0) noundef, ptr addrspace(0) noundef, ptr addrspace(0) noundef) #2

declare i32 @fclose(ptr addrspace(0) noundef) #2

; Function Attrs: nounwind
declare i32 @rename(ptr addrspace(0) noundef, ptr addrspace(0) noundef) #1

; Function Attrs: nounwind
declare i32 @remove(ptr addrspace(0) noundef) #1

declare ptr addrspace(0) @gets(ptr addrspace(0) noundef) #2

declare { double, double } @csin(double noundef, double noundef) #1

declare i32 @getchar() #2
