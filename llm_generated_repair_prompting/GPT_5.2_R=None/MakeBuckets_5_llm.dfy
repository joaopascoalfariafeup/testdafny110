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

// Helper: updating one bucket preserves the "counting" interpretation
// Note: this lemma describes the effect of incrementing the appropriate bucket once.
lemma UpdateBucketPreservesCounts(a: array<nat>, b: array<nat>, i: int, max: nat)
  requires a.Length > 0
  requires 0 <= i < a.Length
  requires b.Length == 1 + max
  requires forall t :: 0 <= t < a.Length ==> a[t] <= max
  requires forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i && a[j] == k|
  modifies b
  ensures forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i+1 && a[j] == k|
{
  var v := a[i];

  assert v <= max;
  assert v < b.Length;

  // Perform the concrete update
  b[v] := b[v] + 1;

  // Prove postcondition by cases on k
  assert forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i+1 && a[j] == k| by
  {
    // For k == v, cardinality increases by exactly 1 (new index i is included).
    // For k != v, set of indices is unchanged.
  }
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
      // One increment per iteration, accounted for by the lemma:
      UpdateBucketPreservesCounts(a, b, i, max);
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
