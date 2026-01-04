// Computes the length (i) of the longest common prefix (initial subarray)
// of two arrays a and b.
method LongestPrefix(a: array<int>, b: array<int>) returns (i: nat)
  requires a != null && b != null
  ensures i <= a.Length && i <= b.Length
  ensures forall k :: 0 <= k < i ==> a[k] == b[k]
  ensures i == a.Length || i == b.Length || a[i] != b[i]
{
  i := 0;
  while i < a.Length && i < b.Length && a[i] == b[i]
    invariant 0 <= i <= a.Length
    invariant 0 <= i <= b.Length
    invariant forall k :: 0 <= k < i ==> a[k] == b[k]
    decreases if a.Length < b.Length then a.Length - i else b.Length - i
  {
    i := i + 1;
  }
}

// Test method with an example.
method testLongestPrefix() {
  var a := new int[] [1, 3, 2, 4, 8];
  var b := new int[] [1, 3, 3, 4];

  // Help Dafny with concrete facts about the arrays
  assert a.Length == 5 && b.Length == 4;
  assert a[0] == b[0];
  assert a[1] == b[1];
  assert a[2] != b[2];

  var i := LongestPrefix(a, b);

  // Prove i >= 2 by ruling out i == 0 and i == 1
  if i == 0 {
    assert i != a.Length && i != b.Length; // since lengths are 5 and 4
    assert a[i] != b[i];                   // from postcondition 3
    assert a[0] == b[0];
    assert false;
  }
  if i == 1 {
    assert i != a.Length && i != b.Length; // since lengths are 5 and 4
    assert a[i] != b[i];                   // from postcondition 3
    assert a[1] == b[1];
    assert false;
  }

  // Prove i <= 2 by ruling out i >= 3 using postcondition 2 at k = 2
  if i >= 3 {
    assert 0 <= 2 < i;
    assert a[2] == b[2]; // from postcondition 2
    assert a[2] != b[2];
    assert false;
  }

  assert i == 2;
}
