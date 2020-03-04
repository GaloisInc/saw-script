int get_val_impl(int *p, int x)
{
  if (x > 0)
  {
    *p = x;
    return 0;
  }
  return 1;
}

int get_val(int *p, int x)
{
  return get_val_impl(p, x);
}

int get_val_default(int x)
{
  int res;
  if (0 == get_val(&res, x))
  {
    return res;
  }
  return 0;
}

