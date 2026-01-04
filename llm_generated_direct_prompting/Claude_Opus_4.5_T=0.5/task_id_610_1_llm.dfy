// Removes the k-th element from the array s and returns a new array with the result.
method RemoveElementAt(s: array<int>, k: nat) returns (v: array<int>)
    requires k < s.Length
    ensures v.Length == s.Length - 1
    ensures forall i :: 0 <= i < k ==> v[i] == s[i]
    ensures forall i :: k <= i < v.Length ==> v[i] == s[i + 1]
    ensures v[..] == s[..k] + s[k+1..]
{
    v := new int[s.Length - 1];
    for i := 0 to k
        invariant v[..i] == s[..i]
    {
        v[i] := s[i];
    }
    for i := k to s.Length - 1
        invariant v[..k] == s[..k]
        invariant forall j :: k <= j < i ==> v[j] == s[j + 1]
        invariant v[k..i] == s[k+1..i+1]
    {
        v[i] := s[i + 1];
    }
}

// Test cases checked statically.
method RemoveElementTest(){
    // Remove middle element
    var a1 := new int[] [1, 1, 2, 3, 4, 4, 5, 1];
    var res1 := RemoveElementAt(a1, 3);
    assert res1[..] == [1, 1, 2, 4, 4, 5, 1];

    // Remove first element
    var res2 := RemoveElementAt(a1, 0);
    assert res2[..] == [1, 2, 3, 4, 4, 5, 1];

    // Remove last element
    var res3 := RemoveElementAt(a1, 7);
    assert res3[..] == [1, 1, 2, 3, 4, 4, 5];
}
