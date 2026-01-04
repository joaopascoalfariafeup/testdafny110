
// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 

// Ghost function to check if an array is sorted
ghost function IsSorted(a: array<int>): bool
  reads a
{
  forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
}

method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires IsSorted(a) && IsSorted(b)
  ensures IsSorted(c)
  ensures c.Length == a.Length + b.Length
  ensures forall k :: 0 <= k < c.Length ==> (k < a.Length ==> c[k] == a[k]) || (k - a.Length < b.Length ==> c[k] == b[k - a.Length])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant i <= a.Length && j <= b.Length
      invariant c.Length == a.Length + b.Length
      invariant forall k :: 0 <= k < i + j ==> (k < i ==> c[k] == a[k]) || (k - i < j ==> c[k] == b[k - i])
      invariant IsSorted(c[..i+j])
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
    assert c[..] == [1, 2, 3, 4, 5];
}

