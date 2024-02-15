predicate ordered(l: seq<int>)
{
  forall i :: 0 <= i < |l| - 1 ==> l[i] <= l[i + 1]
}

lemma tail_ordered(l:seq<int>)
requires |l| > 0
requires ordered(l)
ensures ordered(l[1..])
{
  if !ordered(l[1..])
  {
    assert |l[1..]| == |l| - 1;
    var i :| 0 <= i < |l| - 2 && l[1..][i] > l[1..][i + 1];
    assert l[i+1] > l[i + 2];
    assert false;
  }
}

lemma multisetIn(x:int,l:seq<int>)
ensures x in l <==> multiset(l)[x] > 0
{
}

lemma multisetSum(l:seq<int>,r:seq<int>)
ensures multiset(l) + multiset(r) == multiset(l + r)
{
}

lemma multisetComm(l:seq<int>,r:seq<int>)
ensures multiset(l) + multiset(r) == multiset(r) + multiset(l)
{
}

lemma multisetExt(l:seq<int>,r:seq<int>)
ensures (forall x :: multiset(l)[x] == multiset(r)[x]) ==> multiset(l) == multiset(r)
{
}

function remove(x:int,l:seq<int>):seq<int>
requires x in l
ensures |l| == |remove(x,l)| + 1
{
  if x == l[0] then l[1..] else [l[0]] + remove(x,l[1..])
}

lemma multiset_tail(l:seq<int>,x:int)
requires |l| > 0
ensures multiset(l[1..]) == multiset(l) - multiset([l[0]])
ensures if x == l[0] then multiset(l[1..])[x] == multiset(l)[x] - 1 else multiset(l[1..])[x] == multiset(l)[x]
{
  multisetSum([l[0]],l[1..]);
  assert [l[0]] + l[1..] == l;
  assert multiset([l[0]]) + multiset(l[1..]) == multiset(l);
  // multisetComm(l[1..],[l[0]]);
  assert multiset(l[1..]) + multiset([l[0]]) == multiset(l);
}

lemma multiset_tl(l:seq<int>)
requires |l| > 0
ensures multiset(l[1..]) == multiset(l) - multiset([l[0]])
{
  multiset_tail(l,0);
}

lemma removeLem(x:int,l:seq<int>,y:int)
requires x in l
ensures if x == y then multiset(remove(x,l))[y] == multiset(l)[y] - 1 else multiset(remove(x,l))[y] == multiset(l)[y]
{
  if x == l[0]
  {
    assert remove(x,l) == l[1..];
    multiset_tail(l,x);
  }
  else
  {
    assert x in l[1..];
    removeLem(x,l[1..],y);
    if x == y
    {
      assert multiset(remove(x,l[1..]))[y] == multiset(l[1..])[y] - 1;
      assert [l[0]] + l[1..] == l;
      multisetSum([l[0]],remove(x,l[1..]));
      multisetSum([l[0]],l[1..]);
    }
    else
    {
      assert multiset(remove(x,l[1..]))[y] == multiset(l[1..])[y];
      assert [l[0]] + l[1..] == l;
      multisetSum([l[0]],remove(x,l[1..]));
      multisetSum([l[0]],l[1..]);
    }
  }
}

lemma multisetEqLem(l:seq<int>,o:seq<int>)
decreases |o|
requires |l| == |o|
requires forall i {:trigger i in o} :: i in o ==> multiset(l)[i] == multiset(o)[i]
ensures forall i :: i in l ==> i in o
{
  if |o| == 0 {}
  else
  {
    assert o[0] in o;
    assert multiset(l)[o[0]] == multiset(o)[o[0]];
    assert o[0] in l;
    forall i | i in o[1..]
    ensures multiset(remove(o[0],l))[i] == multiset(o[1..])[i]
    {
      assert i in o;
      assert multiset(l)[i] == multiset(o)[i];
      removeLem(o[0],l,i);
      multiset_tail(o,i);
    }

    multisetEqLem(remove(o[0],l),o[1..]);
    forall i
    ensures i in l ==> i in o
    {
      removeLem(o[0],l,i);
      multiset_tail(o,i);
    }
  }
}

lemma multisetEq(l:seq<int>,o:seq<int>)
requires |l| == |o|
requires forall x {:trigger x in o} :: x in o ==> multiset(l)[x] == multiset(o)[x]
ensures multiset(l) == multiset(o)
{
  forall x
  ensures multiset(l)[x] == multiset(o)[x]
  {
    if !(x in o)
    {
      multisetEqLem(l,o);
      assert multiset(l)[x] == 0;
      assert multiset(o)[x] == 0;
    }
  }
  multisetExt(l,o);
}

lemma multiset_same_len(l:seq<int>,l':seq<int>)
decreases |l|
requires multiset(l) == multiset(l')
ensures |l| == |l'|
{
  if l == []
  {
    if l' != []
    {
      assert l'[0] in l';
      multisetIn(l'[0],l');
      assert !(l'[0] in l);
      multisetIn(l'[0],l);
      assert multiset(l)[l'[0]] != multiset(l')[l'[0]];
      assert false;
    }
    assert l' == [];
  }
  else
  {
    assert l[0] in l;
    assert multiset(l)[l[0]] > 0;
    assert multiset(l)[l[0]] == multiset(l')[l[0]];
    assert l[0] in l';

    forall i
    ensures multiset(remove(l[0],l'))[i] == multiset(l[1..])[i]
    {
      assert multiset(l)[i] == multiset(l')[i];
      removeLem(l[0],l',i);
      multiset_tail(l,i);
    }
    multisetExt(l,l');
    multiset_same_len(l[1..],remove(l[0],l'));
  }
}

lemma ordered_head(l:seq<int>)
requires ordered(l)
requires |l| > 0
ensures forall i :: 0 <= i < |l| ==> l[0] <= l[i]
ensures forall x :: x in l ==> l[0] <= x
{
  ordered_thm_forall(l,0);

  forall x | x in l
  ensures l[0] <= x
  {
    var k :| 0 <= k < |l| && l[k] == x;
    ordered_thm(l,0,k);
  }
}

lemma min_contra_pos(l:seq<int>,y:int,z:int)
requires y in l
requires z in l
requires forall x :: x in l ==> z <= x
ensures y >= z
{
}

lemma min_unique(l:seq<int>,y:int,z:int)
requires y in l
requires forall x :: x in l ==> y <= x
requires z in l
requires forall x :: x in l ==> z <= x
ensures y == z
{
  min_contra_pos(l,y,z);
  min_contra_pos(l,z,y);
}

lemma ordered_head_unique(l:seq<int>,l':seq<int>)
requires ordered(l)
requires ordered(l')
requires multiset(l) == multiset(l')
requires |l| > 0
requires |l'| > 0
ensures l[0] == l'[0]
{
  forall x
  ensures x in l <==> x in l'
  {
    multisetIn(x,l);
    multisetIn(x,l');
  }

  ordered_head(l);
  ordered_head(l');
  assert l[0] in l && l[0] in l';
  assert l'[0] in l' && l'[0] in l;
  min_unique(l,l[0],l'[0]);
  assert l[0] == l'[0];
}

lemma sortedUnique(l:seq<int>,l':seq<int>)
requires ordered(l) && ordered(l') && multiset(l) == multiset(l')
ensures l == l'
{
  if l == [] {
    if l' != []
    {
      assert l'[0] in l';
      multisetIn(l'[0],l');
      assert !(l'[0] in l);
      multisetIn(l'[0],l);
      assert multiset(l)[l'[0]] != multiset(l')[l'[0]];
      assert false;
    }
    assert l' == [];
  }
  else
  {
    assert |l| > 0;
    multiset_tl(l);
    multiset_tl(l');
    assert |l'| > 0;
    
    ordered_head_unique(l,l');
    assert l[0] == l'[0];

    multiset_same_len(l,l');

    tail_ordered(l);
    tail_ordered(l');
    assert ordered(l[1..]);
    assert ordered(l'[1..]);
    sortedUnique(l[1..],l'[1..]);
  }
}


function merge(l:seq<int>,r:seq<int>): seq<int>
ensures ordered(l) && ordered(r) ==> ordered(merge(l,r))
ensures |merge(l,r)| == |l+r|
{
  if |l| == 0
    then r
  else if |r| == 0
    then l
  else if l[0] <= r[0]
    then [l[0]] + merge(l[1..],r)
  else [r[0]] + merge(l,r[1..])
}

lemma merge_preserve(l:seq<int>,r:seq<int>)
ensures multiset(l + r)  == multiset(merge(l,r))
{
  if |l| == 0 {}
  else if |r| == 0 {}
  else if l[0] <= r[0]
  {
    merge_preserve(l[1..],r);
    multisetSum([l[0]],l[1..] + r);
    multisetSum([l[0]],merge(l[1..],r));
    assert [l[0]] + l[1..] == l;
    assert [l[0]] + l[1..] + r == l + r;
    assert [l[0]] + merge(l[1..],r) == merge(l,r);
  }
  else
  {
    merge_preserve(l,r[1..]);
    multisetSum(l,r[1..]);
    multisetSum([r[0]],r[1..]);
    assert [r[0]] + r[1..] == r;
    multisetSum(l,r);
    multisetSum([r[0]],l+r[1..]);
  }
}

function mergeSort(l:seq<int>): seq<int>
ensures |mergeSort(l)| == |l| 
{
  if |l| == 0
    then []
  else if |l| == 1
    then l
  else
    merge(mergeSort(l[..|l|/2]),mergeSort(l[|l|/2..]))
}

lemma mergeSortOrdered(l:seq<int>)
ensures ordered(mergeSort(l))
{
  if |l| == 0 {}
  else if |l| == 1 {}
  else
  {
    mergeSortOrdered(l[..|l|/2]);
    mergeSortOrdered(l[|l|/2..]);
  }
}

lemma mergeSortPreserve(l:seq<int>)
ensures multiset(mergeSort(l)) == multiset(l)
{
  if |l| == 0 {}
  else if |l| == 1 {}
  else
  {
    mergeSortPreserve(l[..|l|/2]);
    mergeSortPreserve(l[|l|/2..]);
    assert l[..|l|/2] + l[|l|/2..] == l;
    multisetSum(l[..|l|/2],l[|l|/2..]);
    merge_preserve(mergeSort(l[..|l|/2]),mergeSort(l[|l|/2..]));
  }
}

datatype Option<T> = Some(t: T) | None

lemma ordered_thm(l:seq<int>,j:nat,i:nat)
requires ordered(l)
requires 0 <= j <= i < |l|
ensures l[j] <= l[i]
decreases i - j
{
  if j < i
  {
    ordered_thm(l,j,i-1);
  }
}

lemma ordered_thm_forall(l:seq<int>,j:nat)
requires ordered(l)
ensures forall i :: j <= i < |l| ==> l[j] <= l[i]
{
  forall i | j <= i < |l|
  {
    ordered_thm(l,j,i);
  }
}

function bsearch(l:seq<int>,x:int): Option<nat>
{
  if |l| == 0
    then None
  else if l[|l|/2] == x
    then Some(|l|/2)
  else if l[|l|/2] < x
    then
      if bsearch(l[|l|/2+1..],x) != None
      then
        Some(|l|/2+1 + bsearch(l[|l|/2+1..],x).t)
      else
        None
  else
    bsearch(l[..|l|/2],x)
}


lemma bsearch_thm(l:seq<int>,x:int)
requires ordered(l)
ensures forall y :: bsearch(l,x) == Some(y) ==>
  0 <= y < |l| &&
  l[y] == x
ensures bsearch(l,x) == None ==>
  (forall i :: 0 <= i < |l| ==> l[i] != x)
{
  if |l| == 0
  {
  }
  else if l[|l|/2] == x
  {
  }
  else if l[|l|/2] < x
  {
    forall j | 0 <= j <= |l|/2
    ensures l[j] < x
    {
      ordered_thm(l,j,|l|/2);
    }
    bsearch_thm(l[|l|/2+1..],x);
  }
  else
  {
    forall j | |l|/2+1 <= j < |l|
    ensures x < l[j]
    {
      ordered_thm(l,|l|/2+1,j);
    }
    bsearch_thm(l[..|l|/2],x);
  }
}
