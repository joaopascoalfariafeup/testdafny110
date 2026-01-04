// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method LongestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
  requires a != null && b != null
  ensures i <= a.Length && i <= b.Length
  ensures forall k: nat :: k < i ==> a[k] == b[k]
  ensures i == a.Length || i == b.Length || a[i] != b[i]
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
      invariant 0 <= i <= a.Length && i <= b.Length
      invariant forall k: nat :: k < i ==> a[k] == b[k]
    {
        i := i + 1;
    }
}
 
// Test method with an example.
method testLongestPrefix() {
    var a := new int[] [1, 3, 2, 4, 8];
    var b := new int[] [1, 3, 3, 4];
    // Add helper assertions to help Dafny verify the test
    assert a[..] == [1, 3, 2, 4, 8];
    assert b[..] == [1, 3, 3, 4];
    assert a[0] == 1 && a[1] == 3 && a[2] == 2 && a[3] == 4 && a[4] == 8;
    assert b[0] == 1 && b[1] == 3 && b[2] == 3 && b[3] == 4;
    var i := LongestPrefix(a, b);
    // Additional proof helper to establish the postcondition
    assert a[2] != b[2]; // a[2] = 2, b[2] = 3
    assert i == 2; 
}



