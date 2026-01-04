
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
      invariant i < a.Length ==> (j == b.Length || a[i] <= b[j]) ==> (i + j == 0 || c[i + j - 1] <= a[i])
      invariant j < b.Length ==> (i == a.Length || b[j] < a[i]) ==> (i + j == 0 || c[i + j - 1] <= b[j])
      invariant c[..i + j] == MergeOrdered(a[..i], b[..j])
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[i + j] := a[i];
            i := i + 1;
        } 
        else {
            c[i + j] := b[j];
            j := j + 1;
        }
    }

}

// Auxiliary function that defines the correct merged sequence
ghost function MergeOrdered(s1: seq<int>, s2: seq<int>): seq<int>
  requires forall k :: 0 <= k < |s1| - 1 ==> s1[k] <= s1[k + 1]
  requires forall k :: 0 <= k < |s2| - 1 ==> s2[k] <= s2[k + 1]
  ensures |MergeOrdered(s1, s2)| == |s1| + |s2|
  ensures forall k :: 0 <= k < |MergeOrdered(s1, s2)| - 1 ==> MergeOrdered(s1, s2)[k] <= MergeOrdered(s1, s2)[k + 1]
  ensures multiset(MergeOrdered(s1, s2)) == multiset(s1) + multiset(s2)
  // ensures MergeOrdered(s1, s2) == MergeOrdered(s2, s1)  // symmetry (not needed but helpful) - removed to avoid termination issues
  decreases |s1| + |s2|
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else if s1[0] <= s2[0] then [s1[0]] + MergeOrdered(s1[1..], s2)
  else [s2[0]] + MergeOrdered(s1, s2[1..])
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
    assert c[..] == MergeOrdered(a[..], b[..]);
    assert c[..] == [1, 2, 3, 4, 5];
}


