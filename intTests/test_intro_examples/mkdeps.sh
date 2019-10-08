grep llvm_load_module *.saw | tr -d '";' | sed -e 's/[a-z_]* <- llvm_load_module//' | sed -e 's/\.saw/.log/' > deps.mk
