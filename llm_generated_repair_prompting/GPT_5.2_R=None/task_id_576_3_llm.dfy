// Helper predicate to avoid brittle quantifiers/triggers on sequence slicing.
ghost predicate SubAt<T>(s: seq<T>, t: seq<T>, i: int)
{
  0 <= i <= |t| - |s| && s == t[i..i+|s|]
}

// Interesting example that previously had a bug for empty lists.
// Checks if a sequence 's' is contained (as a contiguous sublist) in another sequence 't'.
method IsSublist<T(==)>(s: seq<T>, t: seq<T>) returns (result: bool)
  ensures result <==> (exists i :: SubAt(s, t, i))
{
    var n := |t| - |s|;
    if n >= 0 {
        for i := 0 to n + 1
          invariant 0 <= i <= n + 1
          invariant n == |t| - |s|
          invariant forall j :: 0 <= j < i ==> !SubAt(s, t, j)
        {
            if s == t[i.. i+|s|] {
                // Witness for the postcondition on this return path
                assert SubAt(s, t, i);
                return true;
            }
        }
    }
    return false;
}


// Test cases checked statically.
method IsSublistTest(){
    var a0: seq<int> := [1, 0, 2, 2];
    var a1: seq<int> := [1, 2];
    var a2: seq<int> :=  [0, 2, 2];
    var a3: seq<int> := [];

    // Helpful equalities for the verifier (concrete unfolding of definitions)
    assert a0 == [1, 0, 2, 2];
    assert a1 == [1, 2];
    assert a2 == [0, 2, 2];
    assert a3 == [];

    var r1 := IsSublist(a1, a0);
    // Prove !r1 by showing there is no valid witness i
    assert !SubAt(a1, a0, 0);
    assert !SubAt(a1, a0, 1);
    assert !SubAt(a1, a0, 2);
    assert !(exists i :: SubAt(a1, a0, i));
    assert !r1;

    var r2 := IsSublist(a2, a0);
    // Witness i = 1
    assert SubAt(a2, a0, 1);
    assert (exists i :: SubAt(a2, a0, i));
    assert r2;

    var r3 := IsSublist(a3, a0);
    // Empty sequence is always a sublist at i = 0
    assert SubAt(a3, a0, 0);
    assert (exists i :: SubAt(a3, a0, i));
    assert r3;

    var r4 := IsSublist(a3, a3);
    // Empty in empty at i = 0
    assert SubAt(a3, a3, 0);
    assert (exists i :: SubAt(a3, a3, i));
    assert r4;
}
