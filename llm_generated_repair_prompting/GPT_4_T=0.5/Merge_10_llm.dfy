
// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 

// Ghost function to check if a sequence is sorted
ghost function IsSorted(s: seq<int>): bool
{
  forall k :: 0 <= k < |s| - 1 ==> s[k] <= s[k+1]
}

// Ghost function to check if a sequence is a sorted merge of two other sequences
ghost function IsSortedMerge(s: seq<int>, a: seq<int>, b: seq<int>): bool
{
  IsSorted(s) &&
  |s| == |a| + |b| &&
  forall k :: 0 <= k < |s| ==> (k < |a| ==> s[k] == a[k]) || (k >= |a| && k - |a| < |b| ==> s[k] == b[k - |a|])
}

method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires IsSorted(a[..]) && IsSorted(b[..])
  ensures IsSorted(c[..])
  ensures c.Length == a.Length + b.Length
  ensures IsSortedMerge(c[..], a[..], b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant i <= a.Length && j <= b.Length
      invariant c.Length == a.Length + b.Length
      invariant forall k :: 0 <= k < i + j ==> (k < i ==> c[k] == a[k]) || (k >= i && k - i < j ==> c[k] == b[k - i])
      invariant IsSorted(c[..i+j])
      invariant i == 0 || j == 0 || c[i+j-1] == (if a[i-1] <= b[j-1] then a[i-1] else b[j-1])
      decreases a.Length - i + b.Length - j
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];
            i := i + 1;
        } 
        else {
            c[i + j] := b[j];
            j := j + 1;
        }
    }
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert IsSortedMerge(c[..], a[..], b[..]);
    assert c[..] == [1, 2, 3, 4, 5];
}


