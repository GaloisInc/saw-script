library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity PrimeSelector is
    Port (
        clk      : in  std_logic;
        index_in : in  std_logic_vector(3 downto 0); -- 4-bit input index (0 to 15)
        prime_out: out std_logic_vector(7 downto 0)  -- 8-bit output prime
    );
end PrimeSelector;

architecture Behavioral of PrimeSelector is

    -- Define an array of the first 16 prime numbers
    type prime_array_t is array (0 to 15) of integer;
    constant primes : prime_array_t := (
        2, 3, 5, 7, 11, 13, 17, 19,
        23, 29, 31, 37, 41, 43, 47, 53
    );

begin

    process(clk)
        variable idx : integer;
    begin
        if rising_edge(clk) then
            idx := to_integer(unsigned(index_in));
            if idx >= 0 and idx <= 15 then
                prime_out <= std_logic_vector(to_unsigned(primes(idx), 8));
            else
                prime_out <= (others => '0'); -- Default case (shouldn't happen)
            end if;
        end if;
    end process;

end Behavioral;
