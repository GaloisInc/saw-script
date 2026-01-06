unsigned f(unsigned x) {
    // should generate an llvm.stacksave.p0 intrinsic call here
    char s1[x];
    while (1) {
        // should generate an llvm.stacksave.p0 intrinsic call here
        char s2[x];
        if (1) break;
        // should generate an llvm.stackrestore.p0 intrinsic call here
    }
        // should generate an llvm.stackrestore.p0 intrinsic call here
    return x;
}
