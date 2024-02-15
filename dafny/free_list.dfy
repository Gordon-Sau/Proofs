// fixed-sized block free list

datatype Option<T> = Some(t:T) | None

function update_seq(s: seq<Option<int>>,index:nat,x:int): seq<Option<int>>
requires 0 <= index < |s|
requires s[index] != None
{
  s[index := Some(x)]
}

function free_seq(s: seq<Option<int>>,index:nat): seq<Option<int>>
requires 0 <= index < |s|
requires s[index] != None
{
  s[index := None]
}

// use a predicate to state the relations between the input and output
predicate alloc_seq(s: seq<Option<int>>,x:int,index:int,s':seq<Option<int>>)
{
  if (exists i :: 0 <= i < |s| && s[i] == None)
  then (0 <= index < |s| &&
    s[index] == None &&
    s' == s[index := Some(x)])
  else (index == -1 && s' == s)
}

function all_nones(n: nat): seq<Option<int>>
ensures |all_nones(n)| == n
ensures forall i :: 0 <= i < n ==>
  all_nones(n)[i] == None
// decreases n // it is obvious to dafny, so we don't need it
{
  if n == 0
  then []
  else [None] + all_nones(n-1)
}

// a relation between free and free_head
predicate free_ok(fl: seq<int>, fhd: int, buf: seq<int>)
decreases |fl|
{
  -1 <= fhd < |buf| &&
  if |fl| == 0
  then fhd == -1
  else (
    fhd == fl[0] &&
    fhd != -1 &&
    free_ok(fl[1..],buf[fhd],buf)
  )
}

lemma free_ok_independent(fl: seq<int>, fhd: int, buf: seq<int>, upd: nat, x: int)
requires free_ok(fl,fhd,buf)
requires 0 <= upd < |buf|
requires upd !in fl
ensures free_ok(fl,fhd,buf[upd := x])
{
  if |fl| != 0
  {
    free_ok_independent(fl[1..],buf[fhd],buf,upd,x);
  }
}

lemma free_list_unique(fl: seq<int>, fhd: int, buf: seq<int>,fl2: seq<int>)
requires free_ok(fl,fhd,buf)
requires free_ok(fl2,fhd,buf)
ensures fl == fl2
{
  if |fl| != 0
  {
    free_list_unique(fl[1..],buf[fhd],buf,fl2[1..]);
  }
}

lemma free_list_hd_thm(fl: seq<int>, fhd: int, buf: seq<int>)
requires free_ok(fl,fhd,buf)
ensures forall n :: 0 <= n < |fl| ==> free_ok(fl[n..],fl[n],buf)
{
  if |fl| != 0
  {
    if buf[fhd] != -1
    {
      assert |fl| > 1;
      assert buf[fhd] == fl[1];
      free_list_hd_thm(fl[1..],fl[1],buf);
    }
  }
}

lemma free_ok_unique_hd(fl: seq<int>, fhd: int, buf: seq<int>)
requires free_ok(fl,fhd,buf)
requires fhd != -1
ensures forall i :: 0<= i < |fl| && fhd == fl[i] ==> i == 0
{
  
  forall i | (0 <= i < |fl| && fhd == fl[i])
  ensures i == 0
  {
    free_list_hd_thm(fl,fhd,buf);
    assert free_ok(fl[i..],fl[i],buf);
    free_list_unique(fl,fhd,buf,fl[i..]);
  }
}
// to make the proof easier, every data is an (unbouded) integer
class FreeList
{
  ghost var data: seq<Option<int>> // abstraction of the free list
  ghost var free: seq<int>; // list of indices of free slot

  var data_buffer: array<int>;
  var free_head: int;

  // a relation between data and (data_buffer and free)
  // We can actually implement a function to calculate data
  // using data_buffer and free, and without storing data
  // Using ghost variable reminds the us to update data,
  // which helps the smt solver. If we use the function approach, we
  // may need to add assertion to hint the smt solver, which is annoying 
  predicate data_ok()
  reads this, data_buffer
  {
    |data| == data_buffer.Length &&
    (forall i :: 0 <= i < |data| ==>
      if i in free
      then data[i] == None
      else data[i] == Some(data_buffer[i])
    )
  }

  predicate wf()
  reads this, data_buffer
  {
    data_buffer.Length > 0 &&
    free_ok(free,free_head,data_buffer[..]) &&
    data_ok()
  }

  lemma init_thm(fl:seq<int>,fhd:int,buf:seq<int>)
  requires 0 <= |fl| <= |buf|
  requires forall j :: 0 <= j < |buf| ==> buf[j] == j - 1
  requires forall j :: 0 <= j < |fl| ==> fl[j] == fhd - j
  requires fhd  == |fl| - 1
  ensures free_ok(fl,fhd,buf)
  {
    if |fl| != 0
    {
      init_thm(fl[1..],buf[fhd],buf);
    }
  }

  constructor init(n: nat)
  requires n > 0
  ensures wf()
  ensures data == all_nones(n)
  {
    data_buffer := new int[n];
    
    data := all_nones(n);

    new;

    var fhd := -1;
    ghost var fl := [];

    assert data_buffer.Length == n;

    for i := 0 to n
    invariant 0 <= i <= n
    invariant fhd == i-1
    invariant |fl| == i
    invariant forall j :: 0 <= j < |fl| ==>
      fl[j] == i - 1 - j
    invariant data_buffer.Length == n
    invariant forall j :: 0 <= j < i ==>
      data_buffer[j] == j - 1
    modifies data_buffer
    {
      assert 0 <= i < data_buffer.Length;
      data_buffer[i] := fhd;
      fhd := i;
      fl := [fhd] + fl;
    }
    init_thm(fl,fhd,data_buffer[..]);
    // data_buffer.Length == n
    // forall j :: 0 <= j < n ==> data_buffer[j] == j - 1
    // |fl| == n
    // forall j :: 0 <= j < n ==> fl[j] == n - 1 - j
    // fhd == n-1
    free := fl;
    free_head := n - 1;

    forall i | 0 <= i < n
    ensures i in free
    {
      assert fl[n - 1 - i] == i;
    }
  }


  method free_index(index: int)
  modifies this, data_buffer
  requires wf()
  requires index !in free
  requires 0 <= index < |data|
  ensures |data| == |old(data)|
  ensures data_buffer.Length == old(data_buffer).Length
  ensures |data| == data_buffer.Length
  ensures forall i :: 0 <= i < |data| && i != index ==>
    data[i] == old(data)[i]
  ensures forall i :: 0 <= i < |data| && i != index ==>
    data_buffer[i] == old(data_buffer)[i]
  ensures free == [index] + old(free)
  ensures index in free
  ensures data_buffer[index] == old(free_head)
  ensures free_head == index
  ensures data[index] == None
  ensures wf()
  ensures free_seq(old(data),index) == data
  {
    assert free_ok(free,free_head,data_buffer[..]);
    ghost var db := data_buffer[..];
    data_buffer[index] := free_head;
    data := data[index := None];
    free_ok_independent(free,free_head,db,index,free_head);
    free := [index] + free;
    free_head := index;
  }

  method update(index: int,x: int)
  modifies this, data_buffer
  requires wf()
  requires index !in free
  requires 0 <= index < |data|
  ensures |old(data)| == |data|
  ensures data_buffer.Length == old(data_buffer).Length
  ensures |data| == data_buffer.Length
  ensures data_buffer[index] == x
  ensures data[index] == Some(x)
  ensures data_buffer.Length == old(data_buffer).Length
  ensures forall i :: 0 <= i < |data| && i != index ==>
    data_buffer[i] == old(data_buffer)[i]
  ensures forall i :: 0 <= i < |data| && i != index ==>
    data[i] == old(data)[i]
  ensures old(free) == free
  ensures old(free_head) == free_head
  ensures index !in free
  ensures wf()
  ensures update_seq(old(data),index,x) == data
  {
    free_ok_independent(free,free_head,data_buffer[..],index,x);
    data_buffer[index] := x;
    data := data[index := Some(x)];
  }

  // allocate and set the value of the slot to x
  method alloc(x: int) returns (index: int)
  modifies this, data_buffer
  requires wf()
  ensures |old(free)| == 0 ==> (
    index == -1 &&
    data_buffer == old(data_buffer) &&
    free == old(free) &&
    free_head == old(free_head) &&
    data == old(data)
  )
  ensures data_buffer.Length == old(data_buffer).Length
  ensures |data| == |old(data)|
  ensures |data| == data_buffer.Length
  ensures |old(free)| > 0 ==>
    0 <= index < data_buffer.Length &&
    free_head ==
      (if |old(free)| == 1 then -1 else old(free)[1]) &&
    free == old(free)[1..] &&
    data_buffer[index] == x &&
    data == old(data)[index := Some(x)] &&
    (forall i :: 0 <= i < data_buffer.Length &&
      index != i ==>
      data_buffer[i] == old(data_buffer)[i])
  ensures wf()
  ensures alloc_seq(old(data),x,index,data)
  {
    ghost var old_free := free;
    index := free_head;
    assert free_ok(free, index, data_buffer[..]);
    if free_head == -1
    {
      assert |old_free| == 0;
      return index;
    }
    assert |old_free| > 0;
    assert free_ok(free[1..], data_buffer[index], data_buffer[..]);
    free_ok_unique_hd(free,free_head,data_buffer[..]);
    free_head := data_buffer[index];
    assert index == free[0];
    free := free[1..];
    assert index !in free;
    free_ok_independent(free,free_head,data_buffer[..],index,x);
    data_buffer[index] := x;
    data := data[index := Some(x)];
  }
}

