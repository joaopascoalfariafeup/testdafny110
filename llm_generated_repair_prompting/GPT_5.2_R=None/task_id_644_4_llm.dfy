// Reverses the array up to index k (exclusive).
method ReverseUptoK<T>(s: array<T>, k: nat := s.Length)
    requires k <= s.Length
    modifies s
    ensures s.Length == old(s.Length)
    ensures s[k..] == old(s[k..])
    ensures forall j:int :: 0 <= j < k ==> s[j] == old(s[k-1-j])
{
  var i := 0;
  while i < k/2
      invariant 0 <= i <= k/2
      invariant s.Length == old(s.Length)
      invariant s[k..] == old(s[k..])
      // already fixed (left part)
      invariant forall j:int :: 0 <= j < i ==> s[j] == old(s[k-1-j])
      // already fixed (right part)
      invariant forall j:int :: k-i <= j < k ==> s[j] == old(s[k-1-j])
      // middle part not yet moved
      invariant forall j:int :: i <= j < k-i ==> s[j] == old(s[j])
  {
    s[i], s[k-1-i] := s[k-1-i], s[i];
    i := i + 1;
  }

  // Derive full reversal property from the loop invariants (case split on j).
  assert forall j:int :: 0 <= j < k ==> s[j] == old(s[k-1-j])
  by {
    intro j;
    if j < i {
      // left part
    } else if k - i <= j {
      // right part
    } else {
      // middle part unchanged
      assert i <= j < k - i;
      assert k - i <= k;
      assert 0 <= k - 1 - j < k;
      assert k - 1 - j < i; // since j >= k - i
      assert old(s[j]) == old(s[k-1-(k-1-j)]);
      assert s[j] == old(s[j]);
    }
  };

  // Now conclude the desired slice equality.
  assert s[..k] == old(s[..k])[..][..k][..]
  by {
    assert old(s[..k])[..] == old(s[..k]);
    assert old(s[..k])[..][..k] == old(s[..k]);
    assert old(s[..k])[..][..k][..] == old(s[..k]);
    assert forall j:int :: 0 <= j < k ==> s[j] == old(s[..k])[j];
  };
}

// Test cases checked statically.
method ReverseUptoKTest(){
  var a1 := new int[] [3, 2, 1, 4, 5, 6];
  ReverseUptoK(a1, 3);
  assert a1[..] == [1, 2, 3, 4, 5, 6];
  ReverseUptoK(a1, 0);
  assert a1[..] == [1, 2, 3, 4, 5, 6];
  ReverseUptoK(a1, 6);
  assert a1[..] == [6, 5, 4, 3, 2, 1];

  var a2 := new int[] [1];
  ReverseUptoK(a2, 1);
  assert a2[..] == [1];

  var a3 := new int[] [];
  ReverseUptoK(a3, 0);
  assert a3[..] == [];
}
