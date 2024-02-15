datatype Seq<T> = Nil | Cons(head: T, tail: Seq<T>)
datatype Option<T> = None| Some(t: T)

function at<T>(i:nat,s:Seq<T>): Option<T>
{
  if s == Nil then None
  else
    if i == 0 then Some(s.head) else at(i-1,s.tail)
}

function length<T>(s:Seq<T>): nat
{
  if s == Nil then 0 else 1 + length(s.tail)
}

function Seq_map<T,S>(f:T -> S,s:Seq<T>): Seq<S>
{
  if s == Nil then Nil else Cons(f(s.head),Seq_map(f,s.tail))
}

function option_map<T,S>(f:T->S,o:Option<T>):Option<S>
{
  if o == None then None else Some(f(o.t))
}

function upto(i:nat,j:nat):Seq<nat>
decreases j - i
{
  if i < j then Cons(i,upto(i+1,j)) else Nil
}

function genSeq<T>(j:nat,f:nat->T): Seq<T>
{
  Seq_map(f,upto(0,j))
}

function append<T>(s:Seq<T>,t:T): Seq<T>
ensures length(append(s,t)) == length(s) + 1
ensures forall i :: 0 <= i < length(s) ==> at(i,append(s,t)) == at(i,s)
ensures at(length(s),append(s,t)) == Some(t)
{
  if s == Nil then Cons(t,s) else Cons(s.head,append(s.tail,t))
}

function genSeq2<T>(j:nat,f:nat->T): Seq<T>
decreases j
ensures length(genSeq2(j,f)) == j
ensures forall i :: 0 <= i < j ==> at(i,genSeq2(j,f)) == Some(f(i))
{
  if j == 0 then Nil else append(genSeq2(j-1,f),f(j-1))
}

lemma {:induction false} map_at<T,S>(f:T -> S, s:Seq<T>)
ensures forall i :nat :: at(i,Seq_map(f,s)) == option_map(f,at(i,s))
{
  if s == Nil {}
  else
  {
    map_at(f,s.tail);
  }
}

lemma {:induction false} gt_length<T>(s:Seq<T>)
ensures forall i :nat :: length(s) <= i ==> at(i,s) == None
{
  if s == Nil
  {
    assert length(s) == 0;
    forall i | length(s) <= i
    ensures length(s) <= i ==> at(i,s) == None
    {
      assert at(i,s) == None;
    }
  } else
  {
    gt_length(s.tail);
    forall i | length(s) <= i
    ensures length(s) <= i ==> at(i,s) == None
    {
      if i == 0
      {
        assert length(s) == 0;
        assert s == Nil;
      }
      else
      {
        assert at(i,s) == at(i-1,s.tail);
      }
    }
  }
}


lemma {:induction false} lt_length<T>(s: Seq<T>)
ensures forall i :: 0 <= i < length(s) ==> exists t :: at(i,s) == Some(t)
decreases length(s)
{
  if length(s) == 0
  {
    assert s == Nil;
  }
  else if length(s) == 1
  {
    assert s != Nil;
    assert at(0,s) == Some(s.head);
  } else
  {
    assert s != Nil;
    assert length(s) > 1;
    assert at(0,s) == Some(s.head);
    lt_length(s.tail);
    forall i | 1 <= i < length(s)
    ensures exists t :: at(i,s) == Some(t)
    {
      assert at(i,s) == at(i-1,s.tail);
    }
  }
}

lemma {:induction false} upto_length(i:nat,j:nat)
ensures i < j ==> length(upto(i,j)) == j - i
ensures j <= i ==> length(upto(i,j)) == 0
decreases j - i
{
  if i < j
  {
    upto_length(i+1,j);
  }
}


lemma {:induction false} upto_lemma(i:nat,j:nat,k:nat)
ensures k < j - i ==> at(k,upto(i,j)) == Some(i+k)
decreases j - i
{
  if j <= i
  {
    assert j - i <= 0;
    assert j - i <= k;
  }
  else
  {
    if k == 0
    {
      assert at(0,upto(i,j)) == Some(i);
    }
    else
    {
      upto_lemma(i+1,j,k-1);
      assert at(k,upto(i,j)) == at(k-1,upto(i+1,j));
    }
  }
}


lemma {:induction false} Seq_thm<T>(i:nat,j:nat,f:nat -> T)
requires i < j
ensures at(i,genSeq(j,f)) == Some(f(i));
{
  assert genSeq(j,f) == Seq_map(f,upto(0,j));
  map_at(f,upto(0,j));
  assert at(i,genSeq(j,f)) == option_map(f,at(i,upto(0,j)));
  upto_lemma(0,j,i);
  assert at(i,upto(0,j)) == Some(i);
}

lemma {:induction false} Seq_None<T>(i:nat,j:nat,f:nat -> T)
requires j <= i
ensures at(i,genSeq(j,f)) == None
{
  assert genSeq(j,f) == Seq_map(f,upto(0,j));
  map_at(f,upto(0,j));
  upto_length(0,j);
  assert length(upto(0,j)) == j;
  gt_length(upto(0,j));
}

lemma {:induction false} at_thm<T>(s: Seq<T>,t: Seq<T>)
requires forall i :nat :: at(i,s) == at(i,t)
ensures s == t
{
  if s == Nil
  {
    assert at(0,t) == None;
    assert t == Nil;
  }
  else
  {
    if t == Nil
    {
      assert at(0,s) == Some(s.head);
      assert at(0,t) == None;
      assert false;
    }
    else
    {
      assert at(0,s) == Some(s.head);
      assert at(0,t) == Some(t.head);
      assert s.head == t.head;
      forall j:nat
      ensures at(j,s.tail) == at(j,t.tail)
      {
        assert at(j + 1,s) == at(j,s.tail);
      }
      at_thm(s.tail,t.tail);
      assert s.tail == t.tail;
    }
  }
}

lemma {:induction false} at_length_thm<T>(s:Seq<T>,t:Seq<T>)
requires length(s) == length(t)
requires forall i :: 0 <= i < length(s) ==> at(i,s) == at(i,t)
ensures s == t
{
  gt_length(s);
  gt_length(t);
  forall i:nat
  ensures at(i,s) == at(i,t)
  {
    if length(s) <= i
    { 
      assert at(i,s) == None;
      assert at(i,t) == None;
    }
  }
  at_thm(s,t);
}

