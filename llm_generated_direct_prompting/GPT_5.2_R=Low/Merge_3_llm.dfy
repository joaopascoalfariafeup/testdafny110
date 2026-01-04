
predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function {:fuel 20} MergeFrom(sa: seq<int>, ia: int, sb: seq<int>, ib: int): seq<int>
  requires 0 <= ia <= |sa|
  requires 0 <= ib <= |sb|
  ensures |MergeFrom(sa, ia, sb, ib)| == (|sa| - ia) + (|sb| - ib)
{
  if ia == |sa| then sb[ib..]
  else if ib == |sb| then sa[ia..]
  else if sa[ia] <= sb[ib] then [sa[ia]] + MergeFrom(sa, ia + 1, sb, ib)
  else [sb[ib]] + MergeFrom(sa, ia, sb, ib + 1)
}

lemma {:fuel 20} MergeFromSorted(sa: seq<int>, ia: int, sb: seq<int>, ib: int)
  requires 0 <= ia <= |sa|
  requires 0 <= ib <= |sb|
  requires Sorted(sa)
  requires Sorted(sb)
  ensures Sorted(MergeFrom(sa, ia, sb, ib))
  decreases (|sa| - ia) + (|sb| - ib)
{
  if ia == |sa| {
  } else if ib == |sb| {
  } else if sa[ia] <= sb[ib] {
    MergeFromSorted(sa, ia + 1, sb, ib);
  } else {
    MergeFromSorted(sa, ia, sb, ib + 1);
  }
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires Sorted(a[..])
  requires Sorted(b[..])
  ensures c.Length == a.Length + b.Length
  ensures c[..] == MergeFrom(a[..], 0, b[..], 0)
  ensures Sorted(c[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j <= c.Length
      invariant c[..i+j] + MergeFrom(a[..], i, b[..], j) == MergeFrom(a[..], 0, b[..], 0)
      decreases c.Length - (i + j)
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert 0 <= i < a.Length;
            assert 0 <= j <= b.Length;
            if j == b.Length {
              assert MergeFrom(a[..], i, b[..], j) == [a[i]] + MergeFrom(a[..], i + 1, b[..], j);
            } else {
              assert 0 <= j < b.Length;
              assert a[i] <= b[j];
              assert MergeFrom(a[..], i, b[..], j) == [a[i]] + MergeFrom(a[..], i + 1, b[..], j);
            }

            c[j + i] := a[i];

            assert c[..i+j] + [a[i]] == c[..i+j+1];

            i := i + 1;

            assert c[..i+j] + MergeFrom(a[..], i, b[..], j) == MergeFrom(a[..], 0, b[..], 0);
        } 
        else {
            assert 0 <= j < b.Length;
            assert 0 <= i <= a.Length;
            if i == a.Length {
              assert MergeFrom(a[..], i, b[..], j) == [b[j]] + MergeFrom(a[..], i, b[..], j + 1);
            } else {
              assert 0 <= i < a.Length;
              assert !(a[i] <= b[j]);
              assert MergeFrom(a[..], i, b[..], j) == [b[j]] + MergeFrom(a[..], i, b[..], j + 1);
            }

            c[i + j] := b[j];

            assert c[..i+j] + [b[j]] == c[..i+j+1];

            j := j + 1;

            assert c[..i+j] + MergeFrom(a[..], i, b[..], j) == MergeFrom(a[..], 0, b[..], 0);
        }
    }

    assert i == a.Length && j == b.Length;
    assert MergeFrom(a[..], i, b[..], j) == [];
    assert c[..] == MergeFrom(a[..], 0, b[..], 0);
    MergeFromSorted(a[..], 0, b[..], 0);
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

