
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function {:fuel 20} MergeSeq(a: seq<int>, b: seq<int>): seq<int>
  decreases |a| + |b|
{
  if |a| == 0 then
    b
  else if |b| == 0 then
    a
  else if a[0] <= b[0] then
    [a[0]] + MergeSeq(a[1..], b)
  else
    [b[0]] + MergeSeq(a, b[1..])
}

lemma {:fuel 20} MergeSeqSorted(a: seq<int>, b: seq<int>)
  requires Sorted(a)
  requires Sorted(b)
  ensures Sorted(MergeSeq(a, b))
  decreases |a| + |b|
{
  if |a| == 0 {
  } else if |b| == 0 {
  } else if a[0] <= b[0] {
    MergeSeqSorted(a[1..], b);
    assert Sorted([a[0]] + MergeSeq(a[1..], b));
  } else {
    MergeSeqSorted(a, b[1..]);
    assert Sorted([b[0]] + MergeSeq(a, b[1..]));
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
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            var oi := i;
            var aj := j;
            var ai := a[oi];
            ghost var p := c[..oi+aj];

            c[aj + oi] := ai;
            i := i + 1;

            assert c[..i+j] == p + [ai];

            assert MergeSeq(a[oi..], b[aj..]) == [ai] + MergeSeq(a[i..], b[j..]);
            assert c[..i+j] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..]);
        } 
        else {
            var oi := i;
            var aj := j;
            var bj := b[aj];
            ghost var p := c[..oi+aj];

            c[oi + aj] := bj;
            j := j + 1;

            assert c[..i+j] == p + [bj];

            assert MergeSeq(a[oi..], b[aj..]) == [bj] + MergeSeq(a[i..], b[j..]);
            assert c[..i+j] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..]);
        }
    }

    assert i == a.Length && j == b.Length;
    assert i + j == c.Length;
    assert MergeSeq(a[i..], b[j..]) == [];
    assert c[..] + [] == MergeSeq(a[..], b[..]);
    assert c[..] == MergeSeq(a[..], b[..]);

    MergeSeqSorted(a[..], b[..]);
    assert Sorted(c[..]);
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

