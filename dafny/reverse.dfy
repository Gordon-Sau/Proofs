function reverse_it<T>(s:seq<T>,accum:seq<T>):seq<T>
ensures |reverse_it(s,accum)| == |s| + |accum|
{
  if s == [] then accum else reverse_it(s[1..],[s[0]] + accum)
}

lemma {:induction false} reverse_it_lemma<T>(s:seq<T>,accum:seq<T>)
ensures forall i :: |s| <= i < |s| + |accum| ==>
  reverse_it(s,accum)[i] == accum[i - |s|]
ensures forall i :: 0 <= i < |s| ==>
  reverse_it(s,accum)[i] == s[|s| - i - 1]
{
  if s == [] {}
  else
  {
    reverse_it_lemma(s[1..],[s[0]] + accum);
  }
}

