library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity add10 is
    port(
        clk: in std_logic;
        enable: in std_logic;
        x: in signed(15 downto 0);

        busy: out std_logic;
        ready: out std_logic;
        y: out signed(15 downto 0)
    );
end entity;

architecture rtl of add10 is
    --SIGNALS
    signal counter: signed(7 downto 0) := (others => '0');
    signal buff: signed(15 downto 0) := (others => '0');

    begin
        ready <= '1' when (counter = "00001011") else '0';
        busy  <= '1' when (counter > "00000000") else '0';
        y <= buff;
        
        st: process(clk)
        begin
          if rising_edge(clk) then
            if counter = "00000000" then
              if enable = '1' then
                counter <= "00000001";
                buff <= x;
              else
                counter <= "00000000";
                buff <= "0000000000000000";
              end if;
            elsif counter < "00001011" then
              counter <= counter + 1;
              buff <= buff + 1;
            else
              counter <= "00000000";
              buff <= "0000000000000000";
            end if;
          end if;
        end process;
    end rtl;
