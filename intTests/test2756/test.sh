set -e

# All of the following are equivalent, and they should all succeed.
SAW_IMPORT_PATH=b_dir:c_dir1/c_dir2 $SAW test.saw
$SAW --import-path b_dir:c_dir1/c_dir2 test.saw
$SAW -i b_dir:c_dir1/c_dir2 test.saw
$SAW --import-path b_dir --import-path c_dir1/c_dir2 test.saw
$SAW -i b_dir -i c_dir1/c_dir2 test.saw
