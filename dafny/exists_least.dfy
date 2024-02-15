// To prove: (exists x. P(x)) ==> (exists n. P(n) /\ forall m. m < n ==> !P(m))
method Least(P: nat -> bool) returns (n: nat)
requires exists x : nat :: P(x) // for termination
ensures P(n)
ensures forall m : nat :: m < n ==> !P(m)
{
  ghost var x : nat :| P(x);
  n := 0;
  while !P(n)
  decreases x - n
  invariant n <= x
  invariant forall m : nat :: m < n ==> !P(m)
  {
    n := n + 1;
  }
}

/*
function even(n: nat): bool
{
  n % 2 == 0
}

method Main() {
  var x := Least(even);
  print(x);
}
*/

































/*
method Least(P: nat -> bool) returns (n: nat)
requires exists x : nat :: P(x) // for hilbert choice
ensures P(n)
ensures forall m : nat :: m < n ==> !P(m)
{
  n := 0;
  // hilbert choice (dafny requires us to prove existence)
  ghost var x : nat :| P(x);
  while !P(n)
  invariant forall m : nat :: m < n ==> !P(m)
  decreases (x - n)
  {
    n := n + 1;
  }
}
*/
