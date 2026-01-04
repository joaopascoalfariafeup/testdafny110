function MinNat(m: nat, n: nat): nat {
  if m <= n then m else n
}

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method LongestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
  ensures i <= a.Length
  ensures i <= b.Length
  ensures forall k: int :: 0 <= k < i ==> a[k] == b[k]
  ensures i == a.Length || i == b.Length || (i < a.Length && i < b.Length && a[i] != b[i])
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
      invariant 0 <= i <= a.Length
      invariant 0 <= i <= b.Length
      invariant forall k: int :: 0 <= k < i ==> a[k] == b[k]
      decreases MinNat(a.Length as nat, b.Length as nat) - i
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

