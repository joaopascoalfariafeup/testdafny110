function method LongestPrefixLen(a: seq<int>, b: seq<int>): nat
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 || a[0] != b[0] then 0
  else 1 + LongestPrefixLen(a[1..], b[1..])
}

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method LongestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
  ensures i == LongestPrefixLen(a[..], b[..])
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
      invariant i == LongestPrefixLen(a[..i], b[..i])
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

