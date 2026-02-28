; Function Attrs: nounwind
declare ptr @tmpnam(ptr noundef) #1

declare noalias ptr @tmpfile() #2

; Function Attrs: nounwind
declare i32 @setvbuf(ptr noundef, ptr noundef, i32 noundef, i64 noundef) #1

; Function Attrs: nounwind
declare void @setbuf(ptr noundef, ptr noundef) #1

declare i32 @fputc(i32 noundef, ptr noundef) #2

declare i32 @putc(i32 noundef, ptr noundef) #2

declare i32 @fputs(ptr noundef, ptr noundef) #2

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #3

declare i64 @fwrite(ptr noundef, i64 noundef, i64 noundef, ptr noundef) #2

declare i32 @fflush(ptr noundef) #2

declare i32 @fgetpos(ptr noundef, ptr noundef) #2

declare i64 @ftell(ptr noundef) #2

declare void @rewind(ptr noundef) #2

declare i32 @fseek(ptr noundef, i64 noundef, i32 noundef) #2

declare i32 @fsetpos(ptr noundef, ptr noundef) #2

declare i32 @fgetc(ptr noundef) #2

declare i32 @getc(ptr noundef) #2

declare i32 @ungetc(i32 noundef, ptr noundef) #2

declare ptr @fgets(ptr noundef, i32 noundef, ptr noundef) #2

declare i64 @fread(ptr noundef, i64 noundef, i64 noundef, ptr noundef) #2

; Function Attrs: nounwind
declare i32 @feof(ptr noundef) #1

; Function Attrs: nounwind
declare void @clearerr(ptr noundef) #1

; Function Attrs: nounwind
declare i32 @ferror(ptr noundef) #1

declare i32 @putchar(i32 noundef) #2

declare i32 @puts(ptr noundef) #2

declare noalias ptr @fopen(ptr noundef, ptr noundef) #2

; Function Attrs: cold
declare void @perror(ptr noundef) #4

declare ptr @freopen(ptr noundef, ptr noundef, ptr noundef) #2

declare i32 @fclose(ptr noundef) #2

; Function Attrs: nounwind
declare i32 @rename(ptr noundef, ptr noundef) #1

; Function Attrs: nounwind
declare i32 @remove(ptr noundef) #1

declare ptr @gets(ptr noundef) #2

declare { double, double } @csin(double noundef, double noundef) #1

declare i32 @getchar() #2
