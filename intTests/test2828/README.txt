File `adder_yosys.json` is produced using the directions in the
"Analyzing Hardware Circuits using Yosys" section of the SAW User
Manual.

File `adder_tabby.json` is generated using the following commands in
TabbyCAD:

yosys> read -vhd adder.vhdl
yosys> hierarchy -check -top add4
yosys> write_json adder_tabby.json

TabbyCAD/Verific insert some extra cells of type "$_BUF_" which are
not present in `adder_yosys.json`. This proof script ensures that the
TabbyCAD version can be read and proved equivalent to the plain Yosys
version.
