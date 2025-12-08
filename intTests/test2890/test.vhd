library ieee;
use ieee.std_logic_1164.all;

entity half is
  port (
    a : in std_logic;
    b : in std_logic;
    c : out std_logic;
    s : out std_logic
  );
end half;

architecture halfarch of half is
begin
  c <= a and b;
  s <= a xor b;
end halfarch;

library ieee;
use ieee.std_logic_1164.all;

entity full is
  port (
    a : in std_logic;
    b : in std_logic;
    cin : in std_logic;
    cout : out std_logic;
    s : out std_logic
  );
end full;

architecture fullarch of full is
  signal half0c : std_logic;
  signal half0s : std_logic;
  signal half1c : std_logic;
begin
  half0 : entity work.half port map (a => a, b => b, c => half0c, s => half0s);
  half1 : entity work.half port map (a => half0s, b => cin, c => half1c, s => s);
  cout <= half0c or half1c;
end fullarch;

library ieee;
use ieee.std_logic_1164.all;

entity add4 is
  port (
    a : in std_logic_vector(3 downto 0);
    b : in std_logic_vector(3 downto 0);
    res : out std_logic_vector(3 downto 0)
  );
end add4;

architecture add4arch of add4 is
  signal full0cout : std_logic;
  signal full1cout : std_logic;
  signal full2cout : std_logic;
  signal ignore : std_logic;
begin
  full0 : entity work.full port map (a => a(0), b => b(0), cin => '0', cout => full0cout, s => res(0));
  full1 : entity work.full port map (a => a(1), b => b(1), cin => full0cout, cout => full1cout, s => res(1));
  full2 : entity work.full port map (a => a(2), b => b(2), cin => full1cout, cout => full2cout, s => res(2));
  full3 : entity work.full port map (a => a(3), b => b(3), cin => full2cout, cout => ignore, s => res(3));
end add4arch;
