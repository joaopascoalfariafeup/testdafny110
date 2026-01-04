// Interesting example that previously had a bug for empty lists.
// Checks if a sequence 's' is contained (as a subsequence) in another sequence 't'.

ghost predicate MatchAt<T(==)>(s: seq<T>, t: seq<T>, i: int)
{
    0 <= i <= |t| - |s| && s == t[i.. i+|s|]
}

ghost predicate IsSubsequence<T(==)>(s: seq<T>, t: seq<T>)
{
    exists i {:trigger MatchAt(s, t, i)} :: MatchAt(s, t, i)
}

method IsSublist<T(==)>(s: seq<T>, t: seq<T>) returns (result: bool)
    ensures result == IsSubsequence(s, t)
{
    var n := |t| - |s|;
    if n >= 0 {
        for i := 0 to n + 1
            invariant forall j {:trigger MatchAt(s, t, j)} :: 0 <= j < i ==> !MatchAt(s, t, j)
        {
            if s == t[i.. i+|s|] {
                assert MatchAt(s, t, i);
                return true;
            }
        }
        assert forall j {:trigger MatchAt(s, t, j)} :: 0 <= j <= n ==> !MatchAt(s, t, j);
    }
    return false;
}


// Test cases checked statically.
method IsSublistTest(){
    var a0: seq<int> := [1, 0, 2, 2];
    var a1: seq<int> := [1, 2];
    var a2: seq<int> :=  [0, 2, 2];
    var a3: seq<int> := [];

    var r1 := IsSublist(a1, a0);
    // Check that [1, 2] is not a contiguous subsequence of [1, 0, 2, 2]
    assert !MatchAt(a1, a0, 0) by { assert a0[0..2] == [1, 0]; }
    assert !MatchAt(a1, a0, 1) by { assert a0[1..3] == [0, 2]; }
    assert !MatchAt(a1, a0, 2) by { assert a0[2..4] == [2, 2]; }
    assert !r1; 

    var r2 := IsSublist(a2, a0);
    // Check that [0, 2, 2] is at position 1 in [1, 0, 2, 2]
    assert a0[1..4] == [0, 2, 2];
    assert MatchAt(a2, a0, 1);
    assert r2; 

    var r3 := IsSublist(a3, a0);
    // Empty sequence matches at position 0
    assert a0[0..0] == [];
    assert MatchAt(a3, a0, 0);
    assert r3;

    var r4 := IsSublist(a3, a3);
    // Empty sequence matches empty sequence at position 0
    assert a3[0..0] == [];
    assert MatchAt(a3, a3, 0);
    assert r4;
}
