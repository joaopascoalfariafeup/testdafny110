
function IsSorted(a: array<int>) : bool
{
    forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
    requires IsSorted(a) && IsSorted(b)
    ensures c.Length == a.Length + b.Length
    ensures IsSorted(c)
    ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    ensures forall k :: a.Length <= k < c.Length ==> c[k] == b[k - a.Length]
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant i + j == c.Length
        invariant IsSorted(c[..i+j])
        invariant forall k :: 0 <= k < i ==> c[k] == a[k]
        invariant forall k :: 0 <= k < j ==> c[i+k] == b[k]
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

