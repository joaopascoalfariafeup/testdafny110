// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
   requires a.Length > 0
   ensures b.Length == 1 + (max k | 0 <= k < a.Length :: a[k])
   ensures forall k :: 0 <= k < b.Length ==> b[k] == (count k a[..])
{
   ghost function max(seq: seq<nat>): nat
   {
      if |seq| == 0 then 0
      else if |seq| == 1 then seq[0]
      else
         var m := max(seq[..|seq|-1]);
         if seq[|seq|-1] > m then seq[|seq|-1] else m
   }
   ghost function count(x: nat, seq: seq<nat>): nat
   {
      if |seq| == 0 then 0
      else (if seq[|seq|-1] == x then 1 else 0) + count(x, seq[..|seq|-1])
   }
   var max := a[0];
   for i := 1 to a.Length
      invariant 1 <= i <= a.Length + 1
      invariant forall k | 0 <= k < i :: a[k] <= max
      invariant exists k | 0 <= k < i :: a[k] == max
   {
      if i < a.Length && a[i] > max {
         max := a[i];
      }
   } 

   b := new nat[1 + max];
   forall k | 0 <= k <= max {
     b[k] := 0;
   }
   for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall k | 0 <= k < b.Length :: b[k] == (count k a[..i])
   {
      if i < a.Length {
         b[a[i]] := b[a[i]] + 1; 
      }
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


