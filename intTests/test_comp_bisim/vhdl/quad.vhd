library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity quad is
    port(
        reset: in std_logic;
        clk: in std_logic;

        start: in std_logic;
        busy: out std_logic;

        a: in signed(7 downto 0);
        res: out signed(7 downto 0)
    );
end entity;

architecture rtl of quad is
    --SIGNALS
    signal counter: integer := 0;
    signal buff: signed(7 downto 0) := (others => '0');
    signal start_latch: std_logic := '0';

    begin
        mult: process(clk)
        variable buff2: signed(15 downto 0) := (others => '0');
        begin
            if rising_edge(clk) then
                if reset = '1' then
                    buff <= (others => '0');
                    res <= (others => '0');
                    busy <= '0';
                    start_latch <= '0';
                    counter <= 0;
                else
                    if start_latch = '0' then
                        if start = '1' then
                            counter <= 0;
                            busy <= '1';
                            buff(7 downto 0) <= a;
                            start_latch <= '1';
                        end if;
                    elsif start_latch = '1' then
                        if counter < 2 then
                            buff2 := (buff*2);
                            buff <= buff2(7 downto 0);
                            counter <= counter + 1;
                        elsif counter = 2 then
                            busy <= '0';
                            res <= buff;
                        end if;
                    end if;
                end if;
            end if;
        end process;
    end rtl;

