
// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires a != null && b != null
  requires forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k + 1]
  requires forall k :: 0 <= k < b.Length - 1 ==> b[k] <= b[k + 1]
  ensures c != null
  ensures c.Length == a.Length + b.Length
  ensures forall k :: 0 <= k < c.Length - 1 ==> c[k] <= c[k + 1]
  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
  ensures c[..] == MergeOrdered(a[..], b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      decreases a.Length - i + b.Length - j
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j == |c[..i + j]|
      invariant forall k :: 0 <= k < i + j - 1 ==> c[k] <= c[k + 1]
      invariant multiset(c[..i + j]) == multiset(a[..i]) + multiset(b[..j])
      invariant c[..i + j] == MergeOrdered(a[..i], b[..j])
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[i + j] := a[i];
            // Helper assertions to maintain the invariant about MergeOrdered
            assert a[..i+1] == a[..i] + [a[i]];
            // Use lemma to prove the MergeOrdered equality
            MergeOrderedStepLemma(a[..i], b[..j]);
            assert MergeOrdered(a[..i+1], b[..j]) == [a[i]] + MergeOrdered(a[..i], b[..j]);
            i := i + 1;
        } 
        else {
            c[i + j] := b[j];
            // Helper assertions to maintain the invariant about MergeOrdered
            assert b[..j+1] == b[..j] + [b[j]];
            // Use lemma to prove the MergeOrdered equality
            MergeOrderedStepLemma2(a[..i], b[..j]);
            assert MergeOrdered(a[..i], b[..j+1]) == [b[j]] + MergeOrdered(a[..i], b[..j]);
            j := j + 1;
        }
    }
}

// Auxiliary function that defines the correct merged sequence
ghost function {:fuel 10} MergeOrdered(s1: seq<int>, s2: seq<int>): seq<int>
  requires forall k :: 0 <= k < |s1| - 1 ==> s1[k] <= s1[k + 1]
  requires forall k :: 0 <= k < |s2| - 1 ==> s2[k] <= s2[k + 1]
  ensures |MergeOrdered(s1, s2)| == |s1| + |s2|
  ensures forall k :: 0 <= k < |MergeOrdered(s1, s2)| - 1 ==> MergeOrdered(s1, s2)[k] <= MergeOrdered(s1, s2)[k + 1]
  ensures multiset(MergeOrdered(s1, s2)) == multiset(s1) + multiset(s2)
  decreases |s1| + |s2|
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else if s1[0] <= s2[0] then 
    var rest := MergeOrdered(s1[1..], s2);
    // Prove multiset property for this branch
    // MergeOrderedMultisetLemma(s1[1..], s2);
    [s1[0]] + rest
  else 
    var rest := MergeOrdered(s1, s2[1..]);
    // Prove multiset property for this branch
    // MergeOrderedMultisetLemma(s1, s2[1..]);
    [s2[0]] + rest
}

// Lemma to help prove multiset property for MergeOrdered
lemma MergeOrderedMultisetLemma(s1: seq<int>, s2: seq<int>)
  requires forall k :: 0 <= k < |s1| - 1 ==> s1[k] <= s1[k + 1]
  requires forall k :: 0 <= k < |s2| - 1 ==> s2[k] <= s2[k + 1]
  ensures multiset(MergeOrdered(s1, s2)) == multiset(s1) + multiset(s2)
  decreases |s1| + |s2|
{
  if |s1| == 0 {
    // Base case: trivial
  } else if |s2| == 0 {
    // Base case: trivial
  } else if s1[0] <= s2[0] {
    MergeOrderedMultisetLemma(s1[1..], s2);
    // Now we know: multiset(MergeOrdered(s1[1..], s2)) == multiset(s1[1..]) + multiset(s2)
    // And we have: multiset([s1[0]] + MergeOrdered(s1[1..], s2)) == multiset({s1[0]}) + multiset(MergeOrdered(s1[1..], s2))
    //            == multiset({s1[0]}) + multiset(s1[1..]) + multiset(s2)
    //            == multiset(s1) + multiset(s2)
  } else {
    MergeOrderedMultisetLemma(s1, s2[1..]);
    // Similar reasoning for the other branch
  }
}

// Helper lemma to prove the ordering property of MergeOrdered
lemma MergeOrderedOrderingLemma(s1: seq<int>, s2: seq<int>)
  requires forall k :: 0 <= k < |s1| - 1 ==> s1[k] <= s1[k + 1]
  requires forall k :: 0 <= k < |s2| - 1 ==> s2[k] <= s2[k + 1]
  ensures forall k :: 0 <= k < |MergeOrdered(s1, s2)| - 1 ==> MergeOrdered(s1, s2)[k] <= MergeOrdered(s1, s2)[k + 1]
  decreases |s1| + |s2|
{
  if |s1| == 0 || |s2| == 0 {
    // Base case: trivial
  } else if s1[0] <= s2[0] {
    MergeOrderedOrderingLemma(s1[1..], s2);
  } else {
    MergeOrderedOrderingLemma(s1, s2[1..]);
  }
}

// Lemma to help prove that MergeOrdered is correct for the loop invariant
lemma MergeOrderedStepLemma(s1: seq<int>, s2: seq<int>)
  requires forall k :: 0 <= k < |s1| - 1 ==> s1[k] <= s1[k + 1]
  requires forall k :: 0 <= k < |s2| - 1 ==> s2[k] <= s2[k + 1]
  requires |s1| > 0 && (|s2| == 0 || s1[0] <= s2[0])
  ensures MergeOrdered(s1, s2) == [s1[0]] + MergeOrdered(s1[1..], s2)
  decreases |s1| + |s2|
{
  // This lemma is trivial from the definition of MergeOrdered
  // The condition matches the recursive case in MergeOrdered
  // No body needed - Dafny can prove this automatically
}

lemma MergeOrderedStepLemma2(s1: seq<int>, s2: seq<int>)
  requires forall k :: 0 <= k < |s1| - 1 ==> s1[k] <= s1[k + 1]
  requires forall k :: 0 <= k < |s2| - 1 ==> s2[k] <= s2[k + 1]
  requires |s2| > 0 && (|s1| == 0 || s2[0] < s1[0])
  ensures MergeOrdered(s1, s2) == [s2[0]] + MergeOrdered(s1, s2[1..])
  decreases |s1| + |s2|
{
  // This lemma is trivial from the definition of MergeOrdered
  // The condition matches the recursive case in MergeOrdered
  // No body needed - Dafny can prove this automatically
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    // Helper assertions to help Dafny verify the test
    assert a[..] == [1, 3, 5];
    assert b[..] == [2, 4];
    // Use the ghost function to establish the expected result
    assert MergeOrdered([1, 3, 5], [2, 4]) == [1, 2, 3, 4, 5];
    // Call lemma to help prove multiset property
    MergeOrderedMultisetLemma([1, 3, 5], [2, 4]);
    // Call lemma to help prove ordering property
    MergeOrderedOrderingLemma([1, 3, 5], [2, 4]);
    assert c[..] == MergeOrdered(a[..], b[..]);
    assert c[..] == [1, 2, 3, 4, 5];
}



