// Ghost function to compute the maximum of a non-empty sequence of natural numbers
ghost function {:fuel 3} SeqMax(s: seq<nat>): nat
  requires |s| > 0
  ensures SeqMax(s) in s
  ensures forall i :: 0 <= i < |s| ==> s[i] <= SeqMax(s)
{
  if |s| == 1 then s[0]
  else
    var m := SeqMax(s[..|s|-1]);
    if s[|s|-1] <= m then m else s[|s|-1]
}

// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length >= 1
  ensures b.Length == 1 + SeqMax(a[..])
  ensures forall k :: 0 <= k < b.Length ==> b[k] == |set i | 0 <= i < a.Length && a[i] == k|
{
   var max := a[0];
   for i := 1 to a.Length
     invariant 1 <= i <= a.Length
     invariant max == SeqMax(a[..i])
   {
      if a[i] > max {
         max := a[i];
      }
   }

   b := new nat[1 + max];

   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall t :: 0 <= t < a.Length ==> a[t] <= max
     invariant forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i && a[j] == k|
   {
      // One increment per iteration
      var v := a[i];

      // Help the verifier with bounds
      assert v <= max;
      assert v < b.Length;

      b[v] := b[v] + 1;

      // Re-establish the counting invariant for the next i
      assert forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i+1 && a[j] == k| by
      {
        fix k | 0 <= k < b.Length;
        if k == v {
          // indices counted for k=v grow by exactly the new index i
          assert (set j | 0 <= j < i+1 && a[j] == k)
               == (set j | 0 <= j < i && a[j] == k) + {i};
          assert i !in (set j | 0 <= j < i && a[j] == k);
          assert |(set j | 0 <= j < i+1 && a[j] == k)|
               == |(set j | 0 <= j < i && a[j] == k)| + 1;

          // all buckets except b[v] unchanged, and b[v] increased by 1
          assert b[k] == old(b[k]) + 1;
        } else {
          // sets of indices for k != v unchanged (since a[i]=v)
          assert (set j | 0 <= j < i+1 && a[j] == k)
               == (set j | 0 <= j < i && a[j] == k);
          // bucket b[k] unchanged by the assignment to b[v]
          assert b[k] == old(b[k]);
        }
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
