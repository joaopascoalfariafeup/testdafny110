// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length == 1 + max(a[..])
  ensures forall k :: 0 <= k < b.Length ==> b[k] == count(a[..], k)
{
   var max := a[0];
   for i := 1 to a.Length
     invariant 0 <= i <= a.Length
     invariant max == max(a[..i])
   {
      if a[i] > max {
         max := a[i];
      }
   } 

   b := new nat[1 + max];
   forall k | 0 <= k <= max {
     b[k] := 0;
   }
   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant forall k :: 0 <= k < b.Length ==> b[k] == count(a[..i], k)
   {
      b[a[i]] := b[a[i]] + 1; 
   } 
}

function max(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 0 else max(s[0], max(s[1..]))
}

function max(x: nat, y: nat): nat {
  if x >= y then x else y
}

function count(s: seq<nat>, v: nat): nat
  decreases |s|
{
  if |s| == 0 then 0 else (if s[0] == v then 1 else 0) + count(s[1..], v)
}

// A simple test case (checked statically)
method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    var b1 := MakeBuckets(a1);
    assert b1[..] == [0, 1, 2, 1]; 
    
    var a2 := new nat[] [0];
    var b2 := MakeBuckets(a2);
    assert b2[..] == [1];
}

