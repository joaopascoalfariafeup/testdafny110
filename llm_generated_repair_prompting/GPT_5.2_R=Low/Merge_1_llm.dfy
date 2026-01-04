
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function {:fuel 50} MergeSeq(sa: seq<int>, sb: seq<int>): seq<int>
  decreases |sa| + |sb|
{
  if |sa| == 0 then sb
  else if |sb| == 0 then sa
  else if sa[0] <= sb[0] then [sa[0]] + MergeSeq(sa[1..], sb)
  else [sb[0]] + MergeSeq(sa, sb[1..])
}

lemma MergeSeqMultiset(sa: seq<int>, sb: seq<int>)
  ensures multiset(MergeSeq(sa, sb)) == multiset(sa) + multiset(sb)
  decreases |sa| + |sb|
{
  if |sa| == 0 {
  } else if |sb| == 0 {
  } else if sa[0] <= sb[0] {
    MergeSeqMultiset(sa[1..], sb);
  } else {
    MergeSeqMultiset(sa, sb[1..]);
  }
}

lemma MergeSeqSorted(sa: seq<int>, sb: seq<int>)
  requires Sorted(sa) && Sorted(sb)
  ensures Sorted(MergeSeq(sa, sb))
  decreases |sa| + |sb|
{
  if |sa| == 0 {
  } else if |sb| == 0 {
  } else if sa[0] <= sb[0] {
    MergeSeqSorted(sa[1..], sb);
    assert forall k :: 0 <= k < |MergeSeq(sa[1..], sb)| ==> sa[0] <= MergeSeq(sa[1..], sb)[k];
  } else {
    MergeSeqSorted(sa, sb[1..]);
    assert forall k :: 0 <= k < |MergeSeq(sa, sb[1..])| ==> sb[0] <= MergeSeq(sa, sb[1..])[k];
  }
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires Sorted(a[..])
  requires Sorted(b[..])
  ensures c.Length == a.Length + b.Length
  ensures c[..] == MergeSeq(a[..], b[..])
  ensures Sorted(c[..])
  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j <= c.Length
      invariant c[..i+j] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..])
    {
        assert i + j < c.Length;
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];
            assert a[i..] != [];
            assert MergeSeq(a[i..], b[j..]) == [a[i]] + MergeSeq(a[i+1..], b[j..]);
            i := i + 1;
        } 
        else {
            c[i + j] := b[j];
            assert b[j..] != [];
            assert MergeSeq(a[i..], b[j..]) == [b[j]] + MergeSeq(a[i..], b[j+1..]);
            j := j + 1;
        }
    }

    assert i == a.Length && j == b.Length;
    assert a[i..] == [];
    assert b[j..] == [];
    assert MergeSeq(a[i..], b[j..]) == [];
    assert c[..] == MergeSeq(a[..], b[..]);
    MergeSeqSorted(a[..], b[..]);
    MergeSeqMultiset(a[..], b[..]);
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

