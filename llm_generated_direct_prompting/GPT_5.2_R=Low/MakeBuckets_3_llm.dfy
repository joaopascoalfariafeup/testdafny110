// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
function MaxSeq(s: seq<nat>): nat
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := MaxSeq(s[..|s|-1]);
    if s[|s|-1] > m then s[|s|-1] else m
}

function Count(s: seq<nat>, v: nat): nat
  decreases |s|
{
  if |s| == 0 then 0
  else Count(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length == 1 + MaxSeq(a[..])
  ensures forall k :: 0 <= k <= MaxSeq(a[..]) ==> b[k] == Count(a[..], k)
{
   var max := a[0];
   for i := 1 to a.Length
     invariant 1 <= i <= a.Length
     invariant max == MaxSeq(a[..i])
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
     invariant b.Length == 1 + max
     invariant forall k :: 0 <= k <= max ==> b[k] == Count(a[..i], k)
   {
      b[a[i]] := b[a[i]] + 1; 
   } 
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

