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
      // left part already reversed
      invariant forall j:int :: 0 <= j < i ==> s[j] == old(s[k-1-j])
      // right part already reversed
      invariant forall j:int :: k-i <= j < k ==> s[j] == old(s[k-1-j])
      // middle part not yet moved
      invariant forall j:int :: i <= j < k-i ==> s[j] == old(s[j])
  {
    s[i], s[k-1-i] := s[k-1-i], s[i];
    i := i + 1;
  }

  // The loop invariants already imply the postcondition for all j in [0,k),
  // since after the loop we have i == k/2.
  assert forall j:int :: 0 <= j < k ==> s[j] == old(s[k-1-j]) by
  {
    forall j:int | 0 <= j < k
      ensures s[j] == old(s[k-1-j])
    {
      if j < i {
        // left-part invariant applies
        assert s[j] == old(s[k-1-j]);
      } else if k - i <= j {
        // right-part invariant applies
        assert s[j] == old(s[k-1-j]);
      } else {
        // middle-part: unchanged, and symmetric index is also in the middle
        assert i <= j < k - i;
        assert s[j] == old(s[j]);
        assert i <= k - 1 - j < k - i;
        assert s[k - 1 - j] == old(s[k - 1 - j]);
        assert old(s[j]) == old(s[k - 1 - j]);
      }
    }
  }
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
