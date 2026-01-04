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
    assert a[..] == [1, 3, 2, 4, 8];
    assert b[..] == [1, 3, 3, 4];
    assert a[0] == 1 && a[1] == 3 && a[2] == 2;
    assert b[0] == 1 && b[1] == 3 && b[2] == 3;
    assert a[2] != b[2];
    var i := LongestPrefix(a, b);
    // From postcondition: i <= 5 && i <= 4, so i <= 4
    // From postcondition: forall k :: 0 <= k < i ==> a[k] == b[k]
    // From postcondition: i == 5 || i == 4 || a[i] != b[i]
    // Since a[0]==b[0] and a[1]==b[1], we have i >= 2 is possible
    // Since a[2] != b[2], if i > 2, then a[2] == b[2] would need to hold (contradiction)
    // So i <= 2
    // If i < 2, then either i==0 or i==1
    // If i==0, then a[0] != b[0], but a[0]==b[0]==1, contradiction
    // If i==1, then a[1] != b[1], but a[1]==b[1]==3, contradiction
    // So i == 2
    assert i <= 4;
    assert i < 5 && i < 4 ==> a[i] != b[i];
    assert i >= 2 ==> (a[0] == b[0] && a[1] == b[1]);
    assert a[2] != b[2];
    assert i != 3 && i != 4; // because that would require a[2] == b[2]
    assert i >= 1; // because a[0] == b[0]
    assert i >= 2; // because a[1] == b[1]
    assert i == 2; 
}
