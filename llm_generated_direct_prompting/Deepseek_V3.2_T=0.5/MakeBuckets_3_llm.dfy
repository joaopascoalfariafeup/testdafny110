// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
   requires a.Length > 0
   ensures b.Length == 1 + max(a)
   ensures forall k :: 0 <= k < b.Length ==> b[k] == count(a[..], k)
{
   var max := a[0];
   for i := 1 to a.Length
     invariant 1 <= i <= a.Length + 1
     invariant forall j :: 0 <= j < i ==> a[j] <= max
     invariant exists j :: 0 <= j < i && a[j] == max
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

function max(a: seq<nat>): nat
   requires |a| > 0
{
   if |a| == 1 then a[0] else
      if a[|a|-1] > max(a[..|a|-1]) then a[|a|-1] else max(a[..|a|-1])
}

function count(s: seq<nat>, k: nat): nat
{
   if |s| == 0 then 0 else
      (if s[|s|-1] == k then 1 else 0) + count(s[..|s|-1], k)
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
