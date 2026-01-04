// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures |b| == 1 + Max(a[..])
  ensures forall k :: 0 <= k < |b| ==> b[k] == Count(a[..], k)
{
   var max := a[0];
   for i := 1 to a.Length
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
   {
      b[a[i]] := b[a[i]] + 1; 
   } 
}

// Auxiliary function to get the maximum value in a sequence
function Max(s: seq<nat>): nat
  requires |s| > 0
{
  if |s| == 1 then s[0] else max(s[0], Max(s[1..]))
}

// Auxiliary function to count occurrences of a value in a sequence
function Count(s: seq<nat>, v: nat): nat
{
  if |s| == 0 then 0 else (if s[0] == v then 1 else 0) + Count(s[1..], v)
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
