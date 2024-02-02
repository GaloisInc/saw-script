library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity comp is
    port(
        clk: in std_logic;
        enable: in std_logic;
        x: in signed(15 downto 0);

        busy: out std_logic;
        ready: out std_logic;
        y: out signed(15 downto 0)
    );
end entity;

architecture rtl of comp is

  signal blocked: std_logic := '1';
  
  signal A_busy: std_logic;
  signal A_ready: std_logic;
  signal A_y: signed(15 downto 0);
  signal B_busy : std_logic;
  signal B_ready : std_logic;
  signal B_y : signed (15 downto 0);

  signal A_enable : std_logic;
  
    begin
      A : entity work.pow4 port map(clk, A_enable, x, A_busy, A_ready, A_y);
      B : entity work.add10 port map (clk, A_ready, A_y, B_busy, B_ready, B_y);

      A_enable <= enable and (not blocked);
      busy <= A_busy or B_busy;
      ready <= B_ready;
      y <= B_y;

      st: process(clk)
      begin
        if rising_edge(clk) then
          if B_ready = '1' then
            blocked <= '0';
          elsif enable = '1' then
            blocked <= '1';
          end if;
        end if;
      end process;
    end rtl;
