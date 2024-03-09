include "option.dfy"

codatatype LList<T> = Nil | Cons(hd: T, tl: LList<T>)

function lappend<T>(a: LList<T>, b: LList<T>): LList<T>
{
  match a
  case Nil => b
  case Cons(h,t) => Cons(h,lappend(t,b))
}

/*
greatest predicate bisimilar<T>(a : LList<T>,b: LList<T>)
{
  match a
  case Nil => b == Nil
  case Cons(h,t) => (match b
    case Nil => false
    case Cons(h2,t2) => h=h2 && bisimilar(t,t2))
}

predicate prefix_bisimilar<T>(k:nat,a: LList<T>,b:LList<T>)
{
  if k == 0 then true else
    match a
    case Nil => b == Nil
    case Cons(h,t) => match b
      case Nil => false
      case Cons(h',t') => h = h' && prefix_bisimilar(k-1,t,t') 
}
*/

lemma lappend_assoc_prefix<T>(k:nat,a:LList<T>,b:LList<T>,c:LList<T>)
ensures lappend(lappend(a,b),c) ==#[k] lappend(a,lappend(b,c))
{
  if (k > 0)
  {
    match a {
      case Nil => {
        assert lappend(lappend(Nil,b),c) == lappend(b,c);
        assert lappend(Nil,lappend(b,c)) == lappend(b,c);
      }
      case Cons(h,t) => {
        assert lappend(lappend(Cons(h,t),b),c) == Cons(h,lappend(lappend(t,b),c));
        assert lappend(Cons(h,t),lappend(b,c)) == Cons(h,lappend(t,lappend(b,c)));
        lappend_assoc_prefix(k-1,t,b,c);
      }
    }
  }
}

lemma lappend_assoc_desugar<T>(a:LList<T>,b:LList<T>,c:LList<T>)
ensures lappend(lappend(a,b),c) == lappend(a,lappend(b,c))
{
  forall k:nat {
    lappend_assoc_prefix(k,a,b,c);
  }
}

greatest lemma lappend_assoc<T>(a:LList<T>,b:LList<T>,c:LList<T>)
ensures lappend(lappend(a,b),c) == lappend(a,lappend(b,c))
{
  match a {
    case Nil => {
      assert lappend(lappend(Nil,b),c) == lappend(b,c);
      assert lappend(Nil,lappend(b,c)) == lappend(b,c);
    }
    case Cons(h,t) => {
      assert lappend(lappend(Cons(h,t),b),c) == Cons(h,lappend(lappend(t,b),c));
      assert lappend(Cons(h,t),lappend(b,c)) == Cons(h,lappend(t,lappend(b,c)));
      lappend_assoc(t,b,c);
    }
  }
}

predicate even(n: nat)
{
  n % 2 == 0
}

greatest predicate levery<T>(P:T -> bool,l:LList<T>)
{
  match l
    case Nil => true
    case Cons(h,t) => P(h) && levery(P,t)
}

function inc2(n:nat): LList<nat>
{
  Cons(n,inc2(n+2))
}

greatest lemma levery_even_inc2(n:nat)
requires even(n)
ensures levery(even,inc2(n))
{
  match inc2(n)
    case Nil => assert false;
    case Cons(h,t) =>
      assert t == inc2(n+2);
      assert even(n+2);
      levery_even_inc2(n+2);
}

least predicate lfinite<T>(l:LList<T>)
{
  match l
    case Nil => true
    case Cons(h,t) => lfinite(t)
}

least predicate mem<T>(x:T,l:LList<T>)
{
  match l
    case Nil => false
    case Cons(h,t) => if h == x then true else mem(x,t)
}

function nth<T>(n:nat,l:LList<T>): option<T>
decreases n
{
  match l
    case Nil => None
    case Cons(h,t) => if n == 0 then Some(h) else nth(n-1,t)
}

least lemma mem_imp_exists_nth<T>(x:T,l:LList<T>)
requires mem(x,l)
ensures exists n:nat :: nth(n,l) == Some(x)
{
  match l
    case Nil => assert !mem(x,l);
    case Cons(h,t) =>
      if h == x
      {
        assert nth(0,l) == Some(x);
      } else
      {
        mem_imp_exists_nth(x,t);
        var n:nat :| nth(n,t) == Some(x);
        assert nth(n+1,l) == nth(n,t);
      }
}

least lemma {:induction false} mem_ind<T>(P:(T,LList<T>)->bool,x:T,l:LList<T>)
requires mem(x,l)
requires forall x, xs :: P(x,Cons(x,xs))
requires forall x, y, xs :: P(x,xs) ==> P(x,Cons(y,xs))
ensures P(x,l)
{
  match l
    case Nil => assert !mem(x,l);
    case Cons(h,t) =>
      if h == x
      {
        assert P(h,l);
      }
      else
      {
        mem_ind(P,x,t);
        assert P(x,l);
      }
}

/*
prefix predicate comem<T>(k:nat,x:T,l:LList<T>)
{
  if k == 0 then true else
  match l
    case Nil => false
    case Cons(h,t) => if h == x then true else comem(k-1,x,t)
}
*/

greatest predicate comem<T>(x:T,l:LList<T>)
{
  match l
    case Nil => false
    case Cons(h,t) => if h == x then true else comem(x,t)
}

lemma {:induction false} comemConsBase<T>(x:T,l:LList<T>)
ensures comem(x,Cons(x,l))
{
}

greatest lemma {:induction false} comem_coind<T>(P:(T,LList<T>)->bool,x:T,l:LList<T>)
requires forall x,l :: P(x,l) ==> (exists xs :: l == Cons(x,xs)) || (exists y,xs :: l == Cons(y,xs) && P(x,xs))
requires P(x,l)
ensures comem(x,l)
{
  match l
    case Nil => assert !P(x,l);
    case Cons(h,t) =>
      if h == x
      {
         comemConsBase(x,t);
      }
      else
      {
        assert P(x,t);
        comem_coind(P,x,t);
      }
}

/* comem(x,l) ==> comem#[k](x,l)
   comem#[k](x,l) ==> comem#[k-1](x,l) */
greatest lemma {:induction false} comem_not_lfinite<T>(x:T,l:LList<T>)
ensures !lfinite(l) ==> comem(x,l)
{
  // to prove: forall k :: !lfinite(l) ==> comem#[k](x,l)
  // to prove: !lfinite(l) && k > 0 &&
  // (forall x,l :: !lfinite(l) ==> comem[k-1](x,l)) ==>
  // match l
  //   case Nil => false
  //   case Cons(h,t) => if h == x then true else comem[k-1](x,t)
  match l
    case Nil => assert lfinite(l);
    case Cons(h,t) =>
      if lfinite(t)
      {
        assert lfinite(l);
      } else
      {
        comem_not_lfinite(x,t);
      }
}

lemma {:induction false} comem_not_lfinite_aux<T>(x:T,l:LList<T>)
ensures !lfinite(l) ==> exists y,xs :: l == Cons(y,xs) && !lfinite(xs)
{
  match l
    case Nil => assert lfinite(l);
    case Cons(h,t) =>
      if lfinite(t)
      {
        assert lfinite(l);
      } else
      {
        assert l == Cons(h,t) && !lfinite(t);
      }
}

lemma {:induction false} comem_not_lfinite_coind<T>(x:T,l:LList<T>)
requires !lfinite(l)
ensures comem(x,l)
{
  forall x, l {
    comem_not_lfinite_aux<T>(x,l);
  }
  
  comem_coind((x,l) => !lfinite(l),x,l);
}

