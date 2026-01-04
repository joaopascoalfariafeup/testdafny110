// Ghost function to compute the maximum of a non-empty sequence of natural numbers
ghost function {:fuel 5} SeqMax(s: seq<nat>): nat
  requires |s| > 0
  ensures SeqMax(s) in s
  ensures forall i :: 0 <= i < |s| ==> s[i] <= SeqMax(s)
{
  if |s| == 1 then s[0]
  else
    var m := SeqMax(s[..|s|-1]);
    if s[|s|-1] <= m then m else s[|s|-1]
}

// Predicate to avoid trigger warnings on quantified set-cardinality equalities
ghost predicate BucketUnchanged(a: array<nat>, i: int, k: nat)
  reads a
{
  (|set j | 0 <= j < i+1 && a[j] == k|) == (|set j | 0 <= j < i && a[j] == k|)
}

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

   // Establish that all a[t] are <= max, needed for bounds in the counting loop
   assert forall t :: 0 <= t < a.Length ==> a[t] <= max by
   {
     assert max == SeqMax(a[..a.Length]);
   }

   // base case for counting invariant (new nat[] initializes elements to 0)
   assert forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < 0 && a[j] == k| by
   {
     assert forall k :: 0 <= k < b.Length ==> b[k] == 0;
   }

   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall t :: 0 <= t < a.Length ==> a[t] <= max
     // Exact counting for the prefix processed so far
     invariant forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i && a[j] == k|
   {
      var v := a[i];

      assert v <= max;
      assert v < b.Length;

      // for k != v, membership in the defining set is unchanged when extending bound i -> i+1
      assert forall k:nat :: 0 <= k < b.Length && k != v ==> BucketUnchanged(a, i, k) by
      {
        intro k:nat;
        if 0 <= k < b.Length && k != v {
          assert BucketUnchanged(a, i, k) by
          {
            assert (forall j :: 0 <= j < i+1 && a[j] == k <==> (0 <= j < i && a[j] == k)) by
            {
              intro j;
              if 0 <= j < i+1 && a[j] == k {
                if j < i {
                } else {
                  assert j == i;
                  assert a[i] == v;
                  assert false;
                }
              } else if 0 <= j < i && a[j] == k {
                assert 0 <= j < i+1;
              }
            }
          }
        }
      }

      // for v, the new set is old set plus i (since a[i] == v)
      assert (|set j | 0 <= j < i+1 && a[j] == v|) == (|set j | 0 <= j < i && a[j] == v|) + 1 by
      {
        // show i is newly added and all other indices are unchanged
        assert i in (set j | 0 <= j < i+1 && a[j] == v);
        assert i !in (set j | 0 <= j < i && a[j] == v);
        assert (forall j :: 0 <= j < i ==> (j in (set t | 0 <= t < i+1 && a[t] == v) <==> j in (set t | 0 <= t < i && a[t] == v))) by
        {
          intro j;
          if 0 <= j < i {
            // j < i implies the bounds predicate is the same in both sets
          }
        }
      }

      b[v] := b[v] + 1;

      // re-establish the counting invariant for i+1 (frame reasoning + the two facts above)
      assert forall k :: 0 <= k < b.Length ==> b[k] == |set j | 0 <= j < i+1 && a[j] == k| by
      {
        intro k;
        if k == v {
          // only bucket v changed by +1
        } else {
          // other buckets unchanged; use BucketUnchanged
          assert BucketUnchanged(a, i, k);
        }
      }
   }

   // connect max with SeqMax for the postcondition on b.Length
   assert max == SeqMax(a[..a.Length]);
}

method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    var b1 := MakeBuckets(a1);
    // Help the prover connect the postcondition to this concrete expected array
    assert a1[..] == [1,2,2,3];
    assert b1.Length == 4;
    assert b1[0] == |set i | 0 <= i < a1.Length && a1[i] == 0|;
    assert b1[1] == |set i | 0 <= i < a1.Length && a1[i] == 1|;
    assert b1[2] == |set i | 0 <= i < a1.Length && a1[i] == 2|;
    assert b1[3] == |set i | 0 <= i < a1.Length && a1[i] == 3|;
    // concrete cardinalities
    assert (|set i | 0 <= i < a1.Length && a1[i] == 0|) == 0;
    assert (|set i | 0 <= i < a1.Length && a1[i] == 1|) == 1;
    assert (|set i | 0 <= i < a1.Length && a1[i] == 2|) == 2;
    assert (|set i | 0 <= i < a1.Length && a1[i] == 3|) == 1;
    assert b1[0] == 0 && b1[1] == 1 && b1[2] == 2 && b1[3] == 1;
    assert b1[..] == [0, 1, 2, 1];

    var a2 := new nat[] [0];
    var b2 := MakeBuckets(a2);
    assert a2[..] == [0];
    assert b2.Length == 1;
    assert b2[0] == |set i | 0 <= i < a2.Length && a2[i] == 0|;
    assert (|set i | 0 <= i < a2.Length && a2[i] == 0|) == 1;
    assert b2[0] == 1;
    assert b2[..] == [1];
}
