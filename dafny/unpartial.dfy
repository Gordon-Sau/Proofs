include "option.dfy"

function unpartial_curry<T>(f:T~>T): T~>option<T>
{
  x reads f.reads => if f.requires(x) then Some(f(x)) else None
}

function unpartial<T>(f:T~>T,x:T): option<T>
reads f.reads
ensures unpartial_curry(f)(x) == unpartial(f,x)
{
  if f.requires(x) then Some(f(x)) else None
}
