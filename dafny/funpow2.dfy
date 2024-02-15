include "option.dfy"

function funpow<T(!new)>(n:nat,f:T ~> option<T>,t:T): option<T>
reads f.reads
requires forall x :: f.requires(x)
ensures funpow(n,f,t) == None || f.requires(funpow(n,f,t).t)
ensures n > 0 ==> funpow(n,f,t) == option_bind(f,funpow(n-1,f,t))
{
  if n == 0 then Some(t)
  else
    match funpow(n-1,f,t)
      case Some(y) =>
        assert f.requires(y);
        assert option_bind(f,funpow(n-1,f,t)) == f(y);
        f(y)
      case None =>
        assert option_bind(f,funpow(n-1,f,t)) == None;
        None
}

lemma funpow_None<T(!new)>(n:nat,m:nat,f:T~>option<T>,t:T)
requires forall x :: f.requires(x)
requires funpow(n,f,t) == None
requires n <= m
ensures funpow(m,f,t) == None
{
  if n < m
  {
    assert 0 < m;
    funpow_None(n,m-1,f,t);
  }
  else
  {
    assert n == m;
  }
}

lemma funpow_None_case<T(!new)>(n:nat,f:T~>option<T>,t:T)
requires forall x :: f.requires(x)
requires funpow(n,f,t) == None
ensures funpow(n-1,f,t) == None || f(funpow(n-1,f,t).t) == None
{
}

method funpow_method<T(!new)>(n:nat,f:T~>option<T>,t:T) returns (t':option<T>)
requires forall x :: f.requires(x)
ensures funpow(n,f,t) == t'
{
  t' := Some(t);
  var i: nat := 0;
  while i < n && t' != None
  invariant 0 <= i <= n
  invariant t' == funpow(i,f,t)
  decreases n - i
  {
    match t'
    {
      case None => t' := None;
      case Some(x) => t' := f(x);
    }
    i := i + 1;
  }
  
  if i < n
  {
    assert t' == None;
    assert funpow(i,f,t) == None;
    funpow_None(i,n,f,t);
  }
}

lemma funpow_shift<T(!new)>(n:nat,f:T~>option<T>,t:T,t':T)
requires forall x :: f.requires(x)
requires f(t) == Some(t')
ensures funpow(n,f,t) == None || f.requires(funpow(n,f,t).t)
ensures funpow(n,f,t') == option_bind(f,funpow(n,f,t))
{
  if n == 0 {}
  else
  {
    match funpow(n,f,t) {
      case Some(y) =>
        funpow_shift(n-1,f,t,t');
        assert funpow(n-1,f,t') == option_bind(f,funpow(n-1,f,t));
        assert funpow(n,f,t') == f(y);
      case None => funpow_None(n,n+1,f,t);
    }
  }
}
