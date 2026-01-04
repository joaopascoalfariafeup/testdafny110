
// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 

// This function checks if the array is sorted in increasing order
ghost function IsSorted(a: array<int>): bool
  reads a
{
  forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
}

// This function checks if the array 'c' is a merge of 'a' and 'b'
ghost function IsMerged(a: array<int>, b: array<int>, c: array<int>): bool
  reads a, b, c
{
  c.Length == a.Length + b.Length &&
  forall i :: 0 <= i < a.Length ==> c.Contains(a[i]) &&
  forall i :: 0 <= i < b.Length ==> c.Contains(b[i])
}

method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires IsSorted(a) && IsSorted(b)
  ensures IsMerged(a, b, c) && IsSorted(c)
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant IsMerged(a[..i], b[..j], c[..i+j]) && IsSorted(c[..i+j])
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
    assert c[..] == [1, 2, 3, 4, 5];
}

