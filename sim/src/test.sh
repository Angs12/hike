#!/bin/bash


touch O0_to_m32.txt
for file in `ls -p ../../coreutils/gcc-O0/bin/ | grep -v / `; do
    echo $file: 1>> O0_to_m32.txt
    bap sim ../../coreutils/gcc-O0/bin/$file ../../coreutils/gcc-O0-m32/bin/$file main 1>> O0_to_m32.txt 
done

touch O0_to_03.txt
for file in `ls -p ../../coreutils/gcc-O0/bin/ | grep -v /`; do
    echo $file: 1>> O0_to_03.txt
    bap sim ../../coreutils/gcc-O0/bin/$file ../../coreutils/gcc-O3/bin/$file main 1>> O0_to_03.txt 
done

touch O3_to_m32.txt
for file in `ls -p ../../coreutils/gcc-O3/bin/ | grep -v /`; do
    echo $file: 1>> O3_to_m32.txt
    bap sim ../../coreutils/gcc-O3/bin/$file ../../coreutils/gcc-O0-m32/bin/$file main 1>> O3_to_m32.txt 
done

touch O0_to_arm.txt
for file in `ls -p ../../coreutils/gcc-O0/bin/ | grep -v /`; do
    echo $file: O0_to_arm.txt
    bap sim ../../coreutils/gcc-O0/bin/$file ../../coreutils/aarch64-O0/bin/$file main 1>> O0_to_arm.txt 
done

touch O3_to_arm.txt
for file in `ls -p ../../coreutils/gcc-O3/bin/ | grep -v /`; do
    echo $file: 03_to_arm.txt
    bap sim ../../coreutils/gcc-O3/bin/$file ../../coreutils/aarch64-O0/bin/$file main 1>> O3_to_arm.txt 
done

touch m32_to_arm.txt
for file in `ls -p ../../coreutils/gcc-O0-m32/bin/ | grep -v /`; do
    echo $file: 1>> m32_to_arm.txt
    bap sim ../../coreutils/gcc-O0-m32/bin/$file ../../coreutils/aarch64-O0/bin/$file main 1>> m32_to_arm.txt 
done

touch arm_to_O0.txt
for file in `ls -p ../../coreutils/aarch64-O0/bin/ | grep -v /`; do
    echo $file: 1>> arm_to_O0.txt
    bap sim ../../coreutils/aarch64-O0/bin/file ../../coreutils/gcc-O0/bin/file main 1>> arm_to_O0.txt 
done

