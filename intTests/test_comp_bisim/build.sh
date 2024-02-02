#!/bin/bash

ghdl analyze vhdl/add10.vhd
yosys -m ghdl -s yosys/add10.ys

ghdl analyze vhdl/pow4.vhd
yosys -m ghdl -s yosys/pow4.ys

ghdl analyze vhdl/comp.vhd
yosys -m ghdl -s yosys/comp.ys
