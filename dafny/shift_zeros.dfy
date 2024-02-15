function filter<T>(f: T ~> bool, s:seq<T>):seq<T>
requires forall x :: x in s ==> f.requires(x)
reads f.reads
decreases s
{
  if s == [] then [] else (if f(s[0]) then [s[0]] else []) + filter(f,s[1..])
}

function count<T>(f: T ~> bool, s:seq<T>): nat
requires forall x :: x in s ==> f.requires(x)
reads f.reads
decreases s
{
  if s == [] then 0 else (if f(s[0]) then 1 else 0) + count(f,s[1..])
}

lemma filter_count_append<T>(f: T ~> bool, s:seq<T>, x: T)
requires forall y :: y in s ==> f.requires(y)
requires f.requires(x)
ensures count(f,s + [x]) == count(f,s) + if f(x) then 1 else 0
ensures filter(f,s + [x]) == filter(f,s) + if f(x) then [x] else []
{
  if s == []
  {
  }
  else
  {
    assert (s+[x])[1..] == s[1..] + [x];
    filter_count_append(f,s[1..],x);
  }
}

function repeat<T>(n: nat, t:T): seq<T>
decreases n
ensures |repeat(n,t)| == n
ensures forall x :: x in repeat(n,t) ==> x == t
{
  if n == 0 then [] else [t] + repeat(n-1,t)
}

lemma repeat_append<T>(n:nat,t:T)
ensures repeat(n,t) + [t] == repeat(n+1,t)
{
  
}

method shiftZeros(a: array<int>)
modifies a
ensures a.Length == old(a.Length)
ensures a[..] == filter(x => x != 0, old(a[..])) + repeat(count(x => x == 0, old(a[..])),0)
{
  var replace_pos: nat := 0;
  var read_pos: nat := 0;
  var len: nat := a.Length;
  
  while (read_pos < len)
  modifies a
  invariant a.Length == len
  invariant 0 <= read_pos <= len
  invariant 0 <= replace_pos <= read_pos
  invariant forall x :: replace_pos <= x < len ==> a[x] == old(a[x])
  invariant count(x => x == 0, old(a[..read_pos])) == read_pos - replace_pos
  invariant a[..replace_pos] == filter(x => x != 0, old(a[..read_pos]))
  {
    assert old(a[..read_pos]) + [a[read_pos]] == old(a[..read_pos+1]);
    filter_count_append(x => x == 0, old(a[..read_pos]),a[read_pos]);
    filter_count_append(x => x != 0, old(a[..read_pos]),a[read_pos]);

    if a[read_pos] != 0
    {
      a[replace_pos] := a[read_pos];
      replace_pos := replace_pos + 1;
    }
    read_pos := read_pos + 1;
  }
  assert old(a[..]) == old(a[..len]);

  ghost var i :nat := replace_pos;

  while (replace_pos < len)
  modifies a
  invariant a.Length == len
  invariant i <= replace_pos <= len
  invariant a[..replace_pos] == filter(x => x != 0, old(a[..])) + repeat(replace_pos - i,0)
  {
    repeat_append(replace_pos - i, 0);

    a[replace_pos] := 0;
    replace_pos := replace_pos + 1;
  }
  
}
