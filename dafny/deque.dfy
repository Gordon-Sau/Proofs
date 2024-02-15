// double-ended queue


datatype option<T> = Some(t:T) | None

// requirements
function peek<T>(q: seq<T>, i: nat): option<T>
{
  if i < |q|
  then Some(q[i])
  else None
}

function pop_head<T>(q: seq<T>,cap:nat): option<(T,seq<T>)>
{
  if |q| == 0
  then None
  else Some((q[0],q[1..]))
}

function push_front<T>(q: seq<T>,x: T,cap:nat): option<seq<T>>
{
  if |q| == cap
  then None
  else Some([x] + q)
}

function push_back<T>(q: seq<T>,x:T,cap:nat): option<seq<T>>
{
  if |q| == cap
  then None
  else Some(q + [x])
}

function pop_last<T>(q: seq<T>): option<(T,seq<T>)>
{
  if |q| == 0
  then None
  else Some((q[|q|-1],q[..|q|-1]))
}

// implementation of the abstract data type
class Ring<T(0)>
{
  var cap:nat;
  var buffer:array<T>;
  var head: nat;
  var size: nat;

  predicate wf()
  reads this, buffer
  {
    cap == buffer.Length &&
    0 <= head < buffer.Length &&
    0 <= size <= buffer.Length
  }

  function get_queue(): seq<T>
  requires head < buffer.Length && size <= buffer.Length
  reads this, buffer
  {
    (buffer[head..] + buffer[..head])[..size]
  }

  constructor(capacity:nat)
  requires capacity > 0
  ensures cap == capacity
  ensures buffer.Length == capacity;
  ensures head == 0
  ensures size == 0
  ensures wf()
  ensures get_queue() == []
  {
    cap := capacity;
    head := 0;
    size := 0;
    buffer := new T[capacity];
  }

  constructor copy(capacity:nat,arr:array<T>)
  requires capacity > arr.Length
  requires capacity > 0
  ensures cap == capacity
  ensures size == arr.Length
  ensures head == 0
  ensures buffer.Length == capacity
  ensures forall i :: 0 <= i < arr.Length ==>
    buffer[i] == arr[i]
  ensures wf()
  ensures get_queue() == arr[..]
  {
    cap := capacity;
    buffer := new T[capacity];
    size := arr.Length;
    head := 0;

    new;
    for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==>
      buffer[j] == arr[j]
    modifies buffer
    {
      buffer[i] := arr[i];
    }
  }
  
  function method ring_peek(index: nat): option<T>
  requires wf()
  reads this, buffer
  ensures ring_peek(index) == peek(get_queue(),index)
  {
    if index < size
    then
      if index + head >= cap
        then
          Some(buffer[index + head - cap])
        else
          Some(buffer[index + head])
    else None
  }
  
  function method full(): bool
  reads this
  {
    size == cap
  }
  
  method ring_pop_head() returns (ret:option<T>)
  modifies this, buffer
  requires wf()
  ensures wf()
  ensures ret == None <==> (pop_head(old(get_queue()),cap) == None)
  ensures ret != None ==> get_queue() == old(get_queue())[1..] && 
    pop_head(old(get_queue()),cap) == Some((ret.t,get_queue()))
  {
    if size == 0
    {
      return None;
    } else {
      ret := Some(buffer[head]);
      head := head + 1;
      if head == buffer.Length
      {
        head := 0;
      }
      size := size - 1;
    }
  }

  method ring_push_front(x: T) returns (success:bool)
  modifies this, buffer
  requires wf()
  ensures wf()
  ensures success <==> (get_queue() == [x] + old(get_queue()) &&
    push_front(old(get_queue()),x,cap) == Some(get_queue()))
  ensures !success <==> (push_front(old(get_queue()),x,cap) == None)
  {
    success := !full();
    if success
    {
      if head == 0
      {
        head := cap - 1;
      } else {
        head := head - 1;
      }
      buffer[head] := x;
      size := size + 1;
      assert get_queue() == [x] + old(get_queue());
    }
  }

}
