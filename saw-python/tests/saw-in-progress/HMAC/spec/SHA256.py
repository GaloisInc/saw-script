# TODO (now)

# SHA256.saw
# import "SHA256.cry";

# let check_sha n = do {
#     print (str_concat "Checking imp_correct for byte count " (show n));
#     time (prove_print abc {{ imp_correct : [n][8] -> Bit }});
# };

# for [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] check_sha;
# for [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] check_sha;
# for [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48] check_sha;
# for [49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] check_sha;
# for [65, 127, 128, 129, 1000] check_sha;





