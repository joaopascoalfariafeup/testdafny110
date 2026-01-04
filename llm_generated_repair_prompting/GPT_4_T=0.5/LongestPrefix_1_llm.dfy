// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 

// Auxiliary ghost function to capture the property of common prefix
ghost function CommonPrefix(a: array<int>, b: array<int>, i: nat): bool
{
    forall k :: 0 <= k < i ==> a[k] == b[k]
}

method LongestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
    ensures i <= a.Length && i <= b.Length
    ensures CommonPrefix(a, b, i)
    ensures i == a.Length || i == b.Length || a[i] != b[i]
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
        invariant i <= a.Length
        invariant i <= b.Length
        invariant CommonPrefix(a, b, i)
    {
        i := i + 1;
    }
}
 
// Test method with an example.
method testLongestPrefix() {
    var a := new int[] [1, 3, 2, 4, 8];
    var b := new int[] [1, 3, 3, 4];
    var i := LongestPrefix(a, b);
    assert i == 2; 
}

