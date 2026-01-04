
// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 

// Auxiliary function to check if an array is sorted
function IsSorted(a: array<int>): bool
{
    forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i+1]
}

method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
    requires IsSorted(a) && IsSorted(b)
    ensures c != null && c.Length == a.Length + b.Length
    ensures IsSorted(c)
    ensures forall i :: 0 <= i < a.Length ==> c[i] == a[i] || c[i] in b[..]
    ensures forall i :: 0 <= i < b.Length ==> c[i] == b[i] || c[i] in a[..]
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant c != null && c.Length == a.Length + b.Length
        invariant IsSorted(c[..i+j])
        invariant forall k :: 0 <= k < i ==> c[k] == a[k] || c[k] in b[..]
        invariant forall k :: 0 <= k < j ==> c[k] == b[k] || c[k] in a[..]
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

