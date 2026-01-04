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

  // v is a valid bucket index
  assert v <= max;
  assert v < b.Length;

  // For k != v, the bucket is unchanged and the set definition doesn't change either
  assert forall k :: 0 <= k < b.Length && k != v ==>
    (|set j | 0 <= j < i+1 && a[j] == k|) == (|set j | 0 <= j < i && a[j] == k|) by
  {
    intro k;
    calc {
      |set j | 0 <= j < i+1 && a[j] == k|
      ==
      |set j | (0 <= j < i && a[j] == k) || (j == i && a[j] == k)|;
    }
    // since k != v and v == a[i], the "j==i" case is impossible
    assert a[i] == v;
    assert k != a[i];
    assert ! (a[i] == k);
    assert (set j | 0 <= j < i+1 && a[j] == k) == (set j | 0 <= j < i && a[j] == k);
  };

  // For k == v, the set gains exactly the new index i
  assert (set j | 0 <= j < i+1 && a[j] == v) == (set j | 0 <= j < i && a[j] == v) + {i} by
  {
    assert 0 <= i < i+1;
    assert a[i] == v;
    // show membership equivalence
    assert forall j :: j in (set t | 0 <= t < i+1 && a[t] == v) <==>
                     j in ((set t | 0 <= t < i && a[t] == v) + {i}) by
    {
      intro j;
      if 0 <= j < i+1 && a[j] == v {
        if j == i {
        } else {
          assert j < i;
          assert j in (set t | 0 <= t < i && a[t] == v);
        }
      } else {
        if j in ((set t | 0 <= t < i && a[t] == v) + {i}) {
          if j == i {
            assert 0 <= i < i+1 && a[i] == v;
          } else {
            assert j in (set t | 0 <= t < i && a[t] == v);
            assert 0 <= j < i && a[j] == v;
          }
        }
      }
    }
  };

  // Now do the concrete update and establish the postcondition pointwise
  b[v] := b[v] + 1;

  assert forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i+1 && a[j] == k| by
  {
    intro k;
    if k == v {
      // b[v] increased by 1, and the set gained exactly {i}
      assert b[v] == |set j | 0 <= j < i && a[j] == v| + 1;
      assert |(set j | 0 <= j < i+1 && a[j] == v)| == |(set j | 0 <= j < i && a[j] == v)| + 1;
    } else {
      // b[k] unchanged, and the set unchanged
      assert b[k] == |set j | 0 <= j < i && a[j] == k|;
      assert (|set j | 0 <= j < i+1 && a[j] == k|) == (|set j | 0 <= j < i && a[j] == k|);
    }
  };
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

   // Arrays of nat are initialized to 0, so no explicit initialization loop is needed.

   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall t :: 0 <= t < a.Length ==> a[t] <= max
     invariant forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i && a[j] == k|
   {
      UpdateBucketPreservesCounts(a, b, i, max);
      // matches the algorithm step; lemma already accounted for the effect
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
