// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures fresh(b) 
  ensures b.Length > 0 && b.Length == MaxSeq(a[..]) + 1
  ensures forall k :: 0 <= k < b.Length ==> b[k] == count(k, a[..])
{
   var max := a[0];
   for i := 1 to a.Length
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
   assert a[..] == old(a[..]); // proof helper
   for i := 0 to a.Length
    invariant forall k :: 0 <= k < b.Length ==> b[k] == count(k, a[..i])
   {
      b[a[i]] := b[a[i]] + 1; 
   } 
   assert a[..] == a[..a.Length]; // proof helper
}

// Gets the maximum value in a non-empty sequence 's' of natural numbers.
ghost function MaxSeq(s: seq<nat>) : (result: nat) 
  requires |s| > 0
  ensures result in s && forall k :: 0 <= k < |s| ==> result >= s[k]
{
   if |s| == 1 then s[0] else if s[0] > MaxSeq(s[1..]) then s[0] else MaxSeq(s[1..])
}

// Counts the number of occurrences of 'x' in a sequence 's' of natural numbers.
ghost function count(x: nat, s: seq<nat>) : nat {
   multiset(s)[x]
}

// A simple test case (checked statically)
method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    assert a1[..] == [1, 2, 2, 3]; // helper
    var b1 := MakeBuckets(a1);
    assert b1[..] == [0, 1, 2, 1]; 
    
    var a2 := new nat[] [0];
    assert a2[..] == [0]; // helper
    var b2 := MakeBuckets(a2);
    assert b2[..] == [1];
}
