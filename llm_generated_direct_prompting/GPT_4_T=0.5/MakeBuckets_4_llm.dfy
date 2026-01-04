// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.

// Ghost function to calculate the maximum value in an array.
ghost function MaxArray(a: array<nat>): nat
{
    if a.Length == 1 then a[0] else max(a[0], MaxArray(a[1..]))
}

// Ghost function to count the number of occurrences of 'k' in 'a'.
ghost function Count(a: array<nat>, k: nat): nat
{
    if a.Length == 0 then 0 else (if a[0] == k then 1 else 0) + Count(a[1..], k)
}

method MakeBuckets(a: array<nat>) returns(b: array<nat>)
    requires a.Length > 0
    ensures b.Length == 1 + MaxArray(a)
    ensures forall k :: 0 <= k < b.Length ==> b[k] == Count(a, k)
{
   var max := a[0];
   for i := 1 to a.Length
     invariant 0 <= i <= a.Length
     invariant max <= MaxArray(a[..i])
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
     invariant forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..i], k)
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

