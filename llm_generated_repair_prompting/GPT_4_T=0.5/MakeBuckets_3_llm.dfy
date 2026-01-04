
// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length == 1 + maxSeq(a[..])
  ensures forall k :: 0 <= k < b.Length ==> b[k] == count(a[..], k)
{
   var max := a[0];
   for i := 1 to a.Length - 1
     invariant 0 <= i < a.Length
     invariant max == maxSeq(a[..i])
   {
      max := maxNum(max, a[i]);
   } 

   b := new nat[1 + max];
   forall k | 0 <= k < b.Length {
     b[k] := 0;
   }
   for i := 0 to a.Length - 1
     invariant 0 <= i < a.Length
     invariant forall k :: 0 <= k < b.Length ==> b[k] == count(a[..i], k)
   {
      b[a[i]] := b[a[i]] + 1; 
   } 
}

// Auxiliary functions
function maxNum(x: nat, y: nat): nat
{
  if x > y then x else y
}

function maxSeq(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 0 else maxNum(s[0], maxSeq(s[1..]))
}

function count(s: seq<nat>, x: nat): nat
  decreases |s|
{
  if |s| == 0 then 0 else (if s[0] == x then 1 else 0) + count(s[1..], x)
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

