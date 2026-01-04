
predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function MergeFrom(sa: seq<int>, sb: seq<int>, i: nat, j: nat): seq<int>
  requires i <= |sa|
  requires j <= |sb|
  requires Sorted(sa)
  requires Sorted(sb)
  ensures |MergeFrom(sa, sb, i, j)| == (|sa| - i) + (|sb| - j)
  ensures multiset(MergeFrom(sa, sb, i, j)) == multiset(sa[i..]) + multiset(sb[j..])
  ensures Sorted(MergeFrom(sa, sb, i, j))
  decreases (|sa| - i) + (|sb| - j)
{
  if i == |sa| then
    sb[j..]
  else if j == |sb| then
    sa[i..]
  else if sa[i] <= sb[j] then
    [sa[i]] + MergeFrom(sa, sb, i + 1, j)
  else
    [sb[j]] + MergeFrom(sa, sb, i, j + 1)
}

function MergeSeq(sa: seq<int>, sb: seq<int>): seq<int>
  requires Sorted(sa)
  requires Sorted(sb)
  ensures |MergeSeq(sa, sb)| == |sa| + |sb|
  ensures multiset(MergeSeq(sa, sb)) == multiset(sa) + multiset(sb)
  ensures Sorted(MergeSeq(sa, sb))
{
  MergeFrom(sa, sb, 0, 0)
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires Sorted(a[..])
  requires Sorted(b[..])
  ensures c.Length == a.Length + b.Length
  ensures c[..] == MergeSeq(a[..], b[..])
  ensures Sorted(c[..])
{
    ghost var m := MergeSeq(a[..], b[..]);

    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j <= c.Length
      invariant c.Length == a.Length + b.Length
      invariant |m| == c.Length
      invariant forall k :: 0 <= k < i + j ==> c[k] == m[k]
      invariant multiset(c[..i+j]) == multiset(a[..i]) + multiset(b[..j])
    {
        var t := i + j;
        assert t < c.Length;
        assert t < |m|;
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert j == b.Length || a[i] <= b[j];
            assert m[t] == a[i];
            c[t] := a[i];
            assert c[t] == m[t];
            i := i + 1;
        } 
        else {
            assert j < b.Length;
            assert m[t] == b[j];
            c[t] := b[j];
            assert c[t] == m[t];
            j := j + 1;
        }
        assert forall k :: 0 <= k < i + j ==> c[k] == m[k];
    }

    assert i == a.Length && j == b.Length;
    assert i + j == c.Length;
    assert forall k :: 0 <= k < c.Length ==> c[k] == m[k];
    assert c[..] == m;
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

