
predicate SortedSeq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function {:fuel 10} MergeSeq(sa: seq<int>, sb: seq<int>): seq<int>
  decreases |sa| + |sb|
{
  if |sa| == 0 then sb
  else if |sb| == 0 then sa
  else if sa[0] <= sb[0] then [sa[0]] + MergeSeq(sa[1..], sb)
  else [sb[0]] + MergeSeq(sa, sb[1..])
}

lemma MergeSeqLength(sa: seq<int>, sb: seq<int>)
  ensures |MergeSeq(sa, sb)| == |sa| + |sb|
  decreases |sa| + |sb|
{
  if |sa| == 0 {
  } else if |sb| == 0 {
  } else if sa[0] <= sb[0] {
    MergeSeqLength(sa[1..], sb);
  } else {
    MergeSeqLength(sa, sb[1..]);
  }
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires SortedSeq(a[..])
  requires SortedSeq(b[..])
  ensures c.Length == a.Length + b.Length
  ensures c[..] == MergeSeq(a[..], b[..])
  ensures SortedSeq(c[..])
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
            assert i < a.Length;
            assert j <= b.Length;
            assert a[i..] != [];
            if j == b.Length {
              assert b[j..] == [];
            } else {
              assert b[j..] != [];
              assert a[i..][0] <= b[j..][0];
            }
            assert MergeSeq(a[i..], b[j..]) == [a[i]] + MergeSeq(a[i+1..], b[j..]);

            c[j + i] := a[i];
            i := i + 1;

            assert c[..(i+j)] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..]);
        } 
        else {
            assert j < b.Length;
            assert b[j..] != [];
            if i == a.Length {
              assert a[i..] == [];
            } else {
              assert a[i..] != [];
              assert b[j..][0] < a[i..][0];
            }
            assert MergeSeq(a[i..], b[j..]) == [b[j]] + MergeSeq(a[i..], b[j+1..]);

            c[i + j] := b[j];
            j := j + 1;

            assert c[..(i+j)] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..]);
        }
    }

    assert i == a.Length && j == b.Length;
    assert a[i..] == [];
    assert b[j..] == [];
    assert MergeSeq(a[i..], b[j..]) == [];
    assert c[..] == MergeSeq(a[..], b[..]);
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

