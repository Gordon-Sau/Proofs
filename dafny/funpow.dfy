// ways to make weakest precondition for recusive higher-order function
// This is a way to solve the problem in https://stackoverflow.com/questions/77533599/weakest-preconditions-for-higher-order-recursive-function
// funpow(n,f,t) apply f n times to t
// dafny version: 3.7.1

predicate funpow_pred<T(!new)>(n:nat, f: T ~> T,t: T,t':T)
reads f.reads
{
  (n == 0 && t' == t) ||
  (n > 0 && exists t2 :: funpow_pred(n-1,f,t,t2) &&
    f.requires(t2) && f(t2) == t')
}

lemma funpow_pred_uniq<T(!new)>(n:nat,f: T ~> T, t:T, t1:T, t2:T)
requires funpow_pred(n,f,t,t1)
requires funpow_pred(n,f,t,t2)
ensures t1 == t2
{
  if n == 0
  {
    assert t1 == t;
    assert t2 == t;
  }
  else
  {
    var t3 :| funpow_pred(n-1,f,t,t3);
    forall t4 | funpow_pred(n-1,f,t,t4)
    ensures funpow_pred(n-1,f,t,t4) ==> t4 == t3
    {
      funpow_pred_uniq(n-1,f,t,t3,t4);
    }
    assert t1 == f(t3);
    assert t2 == f(t3);
  }
}

function funpow<T(!new)>(n:nat,f:T~>T,t:T): T
reads f.reads
requires n > 0 ==> exists t'' :: funpow_pred(n-1,f,t,t'') && f.requires(t'')
ensures funpow_pred(n,f,t,funpow(n,f,t))
ensures forall t'' :: funpow_pred(n,f,t,t'') ==> t'' == funpow(n,f,t)
{
  if n == 0 then t
  else
    ghost var t'' :| funpow_pred(n-1,f,t,t'') && f.requires(t'');
    funpow_pred_uniq(n-1,f,t,funpow(n-1,f,t),t'');
    assert funpow(n-1,f,t) == t'';
    f(funpow(n-1,f,t))
}

lemma funpow_req_lem<T(!new)>(n:nat,f:T~>T,t:T)
ensures (n > 0 ==> funpow.requires(n-1,f,t) && f.requires(funpow(n-1,f,t))) == funpow.requires(n,f,t)
{
}

// more interesting lemmas
predicate inrange(i:nat,n:nat)
{
  0 <= i < n
}

predicate exists_funpow_pred<T(!new)>(i:nat,f: T ~> T, t:T)
reads f.reads
{
  exists t' :: funpow_pred(i,f,t,t') && f.requires(t')
}

lemma funpow_pred_forall<T(!new)>(n:nat, f: T ~> T,t: T, t': T)
requires funpow_pred(n,f,t,t')
ensures forall i {:trigger inrange(i,n)} :: 0 <= i < n ==> exists_funpow_pred(i,f,t)
{
  if n == 0
  {
  }
  else
  {
    forall i | 0 <= i < n
    ensures exists_funpow_pred(i,f,t)
    {
      if i == n - 1
      {
        var t' :| funpow_pred(n-1,f,t,t') && f.requires(t');
        assert funpow_pred(i,f,t,t') && f.requires(t');
      }
      else
      {
        var t' :| funpow_pred(n-1,f,t,t') && f.requires(t');
        funpow_pred_forall(n-1,f,t,t');
        assert inrange(i,n-1);
        assert exists t'' :: funpow_pred(i,f,t,t'') && f.requires(t'');
      }
    }
  }
}

lemma {:induction false} funpow_shift<T(!new)>(n:nat,f:T~>T,t:T)
requires f.requires(t)
requires funpow.requires(n,f,f(t))
ensures funpow.requires(n+1,f,t)
ensures funpow(n,f,f(t)) == funpow(n+1,f,t)
{
  if n == 0
  {
    assert funpow(1,f,t) == f(t);
    assert funpow(0,f,f(t)) == f(t);
  }
  else
  {
    assert funpow.requires(n,f,f(t));
    assert exists t'' :: funpow_pred(n-1,f,f(t),t'') && f.requires(t'');
    var t' :| funpow_pred(n-1,f,f(t),t') && f.requires(t');
    assert funpow_pred(n-1,f,f(t),funpow(n-1,f,f(t)));
    funpow_pred_uniq(n-1,f,f(t),t',funpow(n-1,f,f(t)));
    assert t' == funpow(n-1,f,f(t));

    funpow_shift(n-1,f,t);
    assert funpow(n-1,f,f(t)) == funpow(n,f,t);
    assert funpow(n+1,f,t) == f(funpow(n,f,t));
    assert funpow(n,f,f(t)) == f(funpow(n-1,f,f(t)));
    assert funpow(n,f,f(t)) == funpow(n+1,f,t);
  }
}

method {:induction false} funpow_method<T(!new)>(n:nat,f:T~>T,t:T) returns (t':T)
requires funpow.requires(n,f,t)
ensures funpow.requires(n,f,t)
ensures t' == funpow(n,f,t)
{
  t' := t;
  var i:nat := 0;
  if i < n
  {
    assert 0 < n;
    funpow_pred_forall(n,f,t,funpow(n,f,t));
    assert inrange(0,n);
    ghost var t'' :| funpow_pred(0,f,t,t'') && f.requires(t'');
    funpow_pred_uniq(0,f,t,t'',t');
    assert f.requires(t');
  }

  while i < n
  invariant 0 <= i <= n
  invariant funpow.requires(n,f,t)
  invariant funpow.requires(i,f,t)
  invariant t' == funpow(i,f,t)
  invariant i < n ==> f.requires(t')
  decreases n - i
  {
    t' := f(t');
    i := i + 1;
    assert 0 <= i <= n;

    if i == n {}
    else
    {
      funpow_pred_forall(n,f,t,funpow(n,f,t));
      assert inrange(i,n);
      ghost var t'' :| funpow_pred(i,f,t,t'') && f.requires(t'');
      funpow_pred_uniq(i,f,t,t'',t');
    }
  }
}

function foo(n:int):int
requires n < 2
{
  n + 1
}

method Validator()
{
  assert funpow(0,foo,0) == 0;
  funpow_req_lem(1,foo,0);
  assert funpow(1,foo,0) == 1;
  funpow_req_lem(2,foo,0);
  assert funpow(2,foo,0) == 2;
  assert !foo.requires(2);
}
