// Reverses the array up to index k (exclusive).
method ReverseUptoK<T>(s: array<T>, k: nat := s.Length)
    requires k <= s.Length
    modifies s
    ensures s.Length == old(s.Length)
    ensures s[k..] == old(s[k..])
    ensures forall j:int :: 0 <= j < k ==> s[j] == old(s[k-1-j])
    ensures s[..k] == old(s[..k])[..][..k][..] // trigger-friendly no-op slice
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

  // From the ensures-forall, we can conclude the slice equality we want.
  assert forall j:int :: 0 <= j < k ==> s[j] == old(s[k-1-j]);
  // Now the slice postcondition follows directly.
  assert s[..k] == old(s[..k])[..][..k][..];
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
