function sum(n:nat):nat
ensures sum(n) == (n + 1) * n / 2
{
  if n == 0
  then 0
  else n + sum(n-1)
}

method sum_meth(n:nat) returns (a:nat)
ensures a == sum(n)
{
  var i := 0;
  a := 0;
  while (i < n)
  invariant 0 <= i <= n
  invariant a == sum(i)
  decreases n - i
  {
    i := i + 1;
    a := a + i;
  }
  return a;
}

function sum_accum(n:nat, m:nat):nat
ensures sum_accum(n,m) == sum(n) + m
{
  if n == 0
  then m
  else sum_accum(n - 1, m + n)
}

method sum_accum_impl(n:nat,m:nat) returns (a:nat)
ensures sum_accum(n,m) == a
{
  var i := n;
  a := m;
  while (0 < i)
  invariant 0 <= i <= n
  invariant a >= 0
  invariant sum_accum(i,a) == sum_accum(n,m)
  decreases i
  {
    a := a + i;
    i := i - 1;
  }
  return a;
}
