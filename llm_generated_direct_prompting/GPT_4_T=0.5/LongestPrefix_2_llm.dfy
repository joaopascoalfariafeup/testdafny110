// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method LongestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
    requires a != null && b != null
    ensures forall k :: 0 <= k < i ==> a[k] == b[k] // all elements up to i are equal in both arrays
    ensures i <= a.Length && i <= b.Length // i does not exceed lengths of both arrays
    ensures (i == a.Length || i == b.Length || a[i] != b[i]) // i is the length of common prefix
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
        invariant 0 <= i <= a.Length && 0 <= i <= b.Length // i is within bounds of both arrays
        invariant forall k :: 0 <= k < i ==> a[k] == b[k] // all elements up to i are equal in both arrays
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

