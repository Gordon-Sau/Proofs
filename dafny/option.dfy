datatype option<T> = Some(t:T) | None

function method option_case<T,S>(f: T ~> S, g: S, x: option<T>): S
requires x == None || f.requires(x.t)
reads f.reads
{
  match x
    case None => g
    case Some(t) => f(t)
}

function method option_map<T>(f: T ~> T, x:option<T>): option<T>
requires x == None || f.requires(x.t)
reads f.reads
ensures option_case(x requires f.requires(x) reads f.reads => Some(f(x)),None,x) == option_map(f,x)
{
  match x
    case None =>
      assert option_case(x requires f.requires(x) reads f.reads => Some(f(x)),None,x) == None;
      None
    case Some(t) =>
      assert option_case(x requires f.requires(x) reads f.reads => Some(f(x)),None,x) == Some(f(t));
      Some(f(t))
}

function method option_bind<T>(f:T ~> option<T>, x:option<T>): option<T>
reads f.reads
requires x == None || f.requires(x.t)
ensures option_case(x requires f.requires(x) reads f.reads => f(x),None,x) == option_bind(f,x)
{
  match x
    case None =>
      assert option_case(x requires f.requires(x) reads f.reads => f(x),None,x) == None;
      None
    case Some(t) =>
      assert option_case(x requires f.requires(x) reads f.reads => f(x),None,x) == f(t);
      f(t)
}

