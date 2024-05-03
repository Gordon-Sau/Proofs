// original code from https://github.com/secure-foundations/everquic-dafny/blob/master/src/PrivateDLL.dfy

datatype Option<T> = Some(t:T) | None

class PrivateNode<T> {
  var L: PrivateNode?<T>
  var R: PrivateNode?<T>
  var payload:T
  constructor (p:T)
  ensures payload == p
  {
    payload := p;
  }
}

function last<T>(s:seq<T>): T
requires |s| > 0
{
  s[|s|-1]
}

opaque function to_vals<T>(nodes:seq<PrivateNode<T>>): seq<T>
reads nodes
ensures |to_vals(nodes)| == |nodes|
ensures forall i :: 0 <= i < |nodes| ==>
  to_vals(nodes)[i] == nodes[i].payload
{
  if nodes == [] then []
  else [nodes[0].payload] + to_vals(nodes[1..])
}

function find_index<T(==)>(xs: seq<T>, x:T): Option<nat>
ensures x in xs ==>
  exists k :: find_index(xs,x) == Some(k) &&
    0 <= k < |xs| && xs[k] == x &&
    forall j :: 0 <= j < k ==> xs[j] != x
ensures !(x in xs) ==> find_index(xs,x) == None
{
  if xs == []
  then None
  else if xs[0] == x
  then Some(0)
  else
    match find_index(xs[1..],x)
      case None => None
      case Some(k) => Some(k + 1)
}

class CircularLinkedList<T> {
  ghost var Nodes: seq<PrivateNode<T>>  // sequence of nodes in the linked list
  var head:PrivateNode?<T>
  var tail:PrivateNode?<T>

  // Valid() says that the data structure is a proper doubly linked list
  ghost predicate Valid()
  reads this, Nodes
  {
    (|Nodes| == 0 <==> head == tail == null) &&
    (|Nodes| > 0 ==>
      head == Nodes[0] && tail == last(Nodes) &&
      Nodes[0].L == last(Nodes) && last(Nodes).R == Nodes[0] &&
      (forall i {:trigger Nodes[i].L} :: 1 <= i < |Nodes| ==> Nodes[i].L == Nodes[i-1]) &&
      (forall i {:trigger Nodes[i].R} :: 0 <= i < |Nodes|-1 ==> Nodes[i].R == Nodes[i+1])
    ) &&
    (forall i,j :: 0 <= i < j < |Nodes| ==> Nodes[i] != Nodes[j])  // all distinct 
  }

  constructor()
  ensures Valid()
  ensures Nodes == []
  {
    Nodes := [];
    head := null;
    tail := null;
  }

  constructor singleton(n:PrivateNode<T>)
  requires n.L == n && n.R == n
  ensures Valid()
  ensures Nodes == [n]
  {
    Nodes := [n];
    head := n;
    tail := n;
  }

  method append(other: CircularLinkedList<T>)
  requires Valid() && other.Valid()
  requires |other.Nodes| > 0
  requires |Nodes| > 0
  requires forall i, j :: 0 <= i < |Nodes| && 0 <= j < |other.Nodes| ==> Nodes[i] != other.Nodes[j]
  ensures Nodes == old(Nodes) + old(other.Nodes)
  ensures Valid()
  ensures other.Nodes == old(other.Nodes)
  ensures forall n :: (n in Nodes || n in other.Nodes) ==>
    n.payload == old(n.payload)
  ensures to_vals(Nodes) == to_vals(old(Nodes)) + to_vals(old(other.Nodes))
  modifies other.tail`R, other.head`L, this`tail, this.tail`R, this.head`L, this`Nodes
  {
    tail.R := other.head;
    other.head.L := tail;
    tail := other.tail;
    tail.R := head;
    head.L := tail;
    Nodes := Nodes + other.Nodes;
  }

  method split(node: PrivateNode<T>) returns (rest:CircularLinkedList<T>)
  requires Valid()
  requires node in Nodes
  ensures Valid()
  ensures rest.Valid()
  ensures old(Nodes) == Nodes + [node] + rest.Nodes
  ensures node.payload == old(node.payload) && node.L == old(node.L) && node.R == old(node.R)
  ensures fresh(rest)
  ensures forall n :: n in rest.Nodes ==> allocated(n) && n in old(Nodes)
  ensures forall n :: n in old(Nodes) ==> n.payload == old(n.payload)
  ensures to_vals(Nodes + [node] + rest.Nodes) == to_vals(old(Nodes))
  modifies this`head,this`tail,this`Nodes,this.head`L,this.tail`R,node.L`R,node.R`L
  {
    rest := new CircularLinkedList<T>();

    ghost var sk := find_index(Nodes,node);
    
    if node != tail
    {
      rest.head := node.R;
      rest.tail := tail;
      rest.head.L := rest.tail;
      rest.tail.R := rest.head;

      match sk
      {
        case Some(k) => { rest.Nodes := old(Nodes)[k+1..]; }
        case None => { assert false; }
      }
    }

    if node == head
    {
      tail := null;
      head := null;
      Nodes := [];
    } else {
      tail := node.L;
      head.L := tail;
      tail.R := head;

      match sk
      {
        case Some(k) => { Nodes := old(Nodes)[..k]; }
        case None => { assert false; }
      }
    }
  }

}

