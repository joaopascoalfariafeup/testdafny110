// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method LongestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
  ensures i <= a.Length && i <= b.Length
  ensures forall k :: 0 <= k < i ==> a[k] == b[k]
  ensures i == a.Length || i == b.Length || a[i] != b[i]
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
      invariant 0 <= i <= a.Length && 0 <= i <= b.Length
      invariant forall k :: 0 <= k < i ==> a[k] == b[k]
    {
        i := i + 1;
    }
}
 
// Test method with an example.
method testLongestPrefix() {
    var a := new int[] [1, 3, 2, 4, 8];
    var b := new int[] [1, 3, 3, 4];
    assert a[0] == 1 && a[1] == 3 && a[2] == 2;
    var i := LongestPrefix(a, b);
    assert a[0] == b[0] && a[1] == b[1];
    assert i == 2; 
}