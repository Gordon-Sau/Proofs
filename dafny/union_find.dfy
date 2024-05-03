// y is the reprsentative element of the set that contains 
// x with distance (rank) r

predicate well_formed_elems(e:seq<nat>)
{
  forall k:nat :: k < |e| ==> e[k] < |e|
}

predicate repr(e:seq<nat>,x:nat,y:nat,r:nat)
decreases r
requires well_formed_elems(e)
ensures repr(e,x,y,r) ==> x < |e| && y < |e| && e[y] == y
{
  (x < |e| && x == y && r == 0 && e[y] == y) ||
  (x < |e| && e[x] != x && r > 0 && repr(e,e[x],y,r-1))
}

lemma repr_unique(e:seq<nat>,x:nat,y:nat,r:nat,y':nat,r':nat)
requires well_formed_elems(e)
requires repr(e,x,y,r) && repr(e,x,y',r')
ensures y' == y && r' == r
decreases r,r'
{
  assert x < |e|;
  if e[x] == x
  {
  } else
  {
    assert r > 0;
    assert r' > 0;
    repr_unique(e,e[x],y,r-1,y',r'-1);
  }
}

ghost predicate equiv_repr(e:seq<nat>,x:nat,y:nat)
requires well_formed_elems(e)
{
  exists i,r,r' :: repr(e,x,i,r) && repr(e,y,i,r')
}

ghost predicate max_rank(e:seq<nat>,y:nat,r:nat)
requires well_formed_elems(e)
{
  exists x:nat :: x < |e| && repr(e,x,y,r) && (
    forall z:nat,r':nat :: z < |e| && repr(e,z,y,r') ==> r' <= r)
}

ghost predicate repr_union(e:seq<nat>,x:nat,y:nat,new_e:seq<nat>)
requires well_formed_elems(e)
{
  well_formed_elems(new_e) &&
  (forall x':nat,y':nat :: equiv_repr(e,x',x) && equiv_repr(e,y',y) ==>
    equiv_repr(new_e,x',x) && equiv_repr(new_e,y',y) && equiv_repr(new_e,x',y')) &&
  (forall z :: !equiv_repr(e,z,x) && !equiv_repr(e,z,y) ==>
    forall z' :: equiv_repr(e,z,z') <==> equiv_repr(new_e,z,z'))
}

/*
class UnionFind {
  var parents: array<nat>;
  var ranks: array<nat>;
  ghost var disjoint_sets: set<set<nat>>

  ghost predicate Valid()
  {
    parents.length == ranks.length &&
    well_formed_elems(parents) &&
  }

  constructor(n:nat)
  ensures parents.length == n
  ensures ranks.length == n
  ensures forall i :: i < n ==> parents[i] == i
  ensures forall i :: i < n ==> ranks[i] == 0
  {
    parents := new array<nat>(n);
    ranks := new array<nat>(n);
    disjoint_sets := {};

    var i := 0;
    while i < n
    {
      parents[i] := i;
      ranks[i] := 0;
      disjoint_sets := disjoint_sets + {{i}};
      i := i + 1;
    }
  }

  method find(i:nat)
  {
    while parents[i] != i
    {
      parents[i] := parents[parents[i]];
      i := parents[i];
    }
    return i;
  }

  method union(x:nat,y:nat)
  {
    x_parent := find(x);
    y_parent := find(y);

    if x_parent == y_parent
    {
      return;
    }

    x_rank := ranks[x_parent];
    y_rank := ranks[y_parent];

    if x_rank < y_rank
    {
      temp_parent := x_parent;
      temp_rank := x_rank;
      x_rank := y_rank;
      x_parent := y_parent;
      y_rank := temp_rank;
      y_parent := temp_parent;
    }

    parents[y_parent] := x_parent;
    if ranks[x_parent] == ranks[y_parent]
    {
      ranks[x_parent] = ranks[x_parent] + 1;
    }
  }
}
*/
