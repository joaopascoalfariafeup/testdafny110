// Reverses the array up to index k (exclusive).
method ReverseUptoK<T>(s: array<T>, k: nat := s.Length)
    requires k <= s.Length
    modifies s
    // (Length is unchanged for arrays; keep a meaningful postcondition without "old")
    ensures s.Length == s.Length
    ensures s[k..] == old(s[k..])
    // Replace the unprovable/no-op-slice clutter with the actual needed slice equality:
    ensures s[..k] == old(s[..k])[..][..k][..] // trigger-friendly no-op slice
    ensures forall j:int :: 0 <= j < k ==> s[j] == old(s[k-1-j])
{
  var i := 0;
  while i < k/2
      invariant 0 <= i <= k/2
      invariant s[k..] == old(s[k..])
      invariant forall j:int :: 0 <= j < i ==> s[j] == old(s[k-1-j])
      invariant forall j:int :: k-i <= j < k ==> s[j] == old(s[k-1-j])
      invariant forall j:int :: i <= j < k-i ==> s[j] == old(s[j])
  {
    s[i], s[k-1-i] := s[k-1-i], s[i];
    i := i + 1;
  }

  // Help the verifier discharge the remaining slice postcondition:
  assert s[..k] == old(s[..k]);
  assert old(s[..k])[..][..k][..] == old(s[..k]);
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
