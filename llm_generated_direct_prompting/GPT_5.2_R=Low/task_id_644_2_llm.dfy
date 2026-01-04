// Reverses the array up to index k (exclusive).
method ReverseUptoK<T>(s: array<T>, k: nat := s.Length)
    modifies s
    requires k <= s.Length
    ensures s.Length == old(s.Length)
    ensures forall j:int :: 0 <= j < k ==> s[j] == old(s[..])[k - 1 - j]
    ensures forall j:int :: k <= j < s.Length ==> s[j] == old(s[..])[j]
{
	var i := 0; 
	while i < k/2
        invariant 0 <= i <= k/2
        invariant forall j:int :: 0 <= j < i ==> s[j] == old(s[..])[k - 1 - j]
        invariant forall j:int :: 0 <= j < i ==> s[k - 1 - j] == old(s[..])[j]
        invariant forall j:int :: i <= j < k - i ==> s[j] == old(s[..])[j]
        invariant forall j:int :: k <= j < s.Length ==> s[j] == old(s[..])[j]
        decreases k/2 - i
	{
		s[i], s[k-1-i] := s[k-1-i], s[i];
		i := i + 1;
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
