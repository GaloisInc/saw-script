struct s {
  unsigned x:1;
  unsigned y:1;
};

int f(const struct s *ss) {
  return ss->x == ss->y;
}
