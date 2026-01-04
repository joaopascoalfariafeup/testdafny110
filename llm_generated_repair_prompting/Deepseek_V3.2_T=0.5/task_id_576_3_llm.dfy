// Interesting example that previously had a bug for empty lists.
// Checks if a sequence 's' is contained (as a subsequence) in another sequence 't'.

// Helper predicate to provide a trigger for the quantifier
ghost predicate IsMatchAt<T(==)>(s: seq<T>, t: seq<T>, i: int)
  requires 0 <= i <= |t| - |s|
{
  s == t[i.. i+|s|]
}

method IsSublist<T(==)>(s: seq<T>, t: seq<T>) returns (result: bool)
  ensures result == exists i :: 0 <= i <= |t| - |s| && IsMatchAt(s, t, i)
{
    var n := |t| - |s|;
    if n >= 0 {
        for i := 0 to n + 1
          invariant 0 <= i <= n+1
          invariant forall j :: 0 <= j < i ==> !IsMatchAt(s, t, j)
        {
            if s == t[i.. i+|s|] {
                // Prove postcondition when returning true
                assert 0 <= i <= |t| - |s|;
                assert IsMatchAt(s, t, i);
                assert exists i :: 0 <= i <= |t| - |s| && IsMatchAt(s, t, i);
                return true;
            }
        }
        // After loop: i == n+1
        assert i == n+1;
        // Show that no i in range satisfies the condition
        assert forall j :: 0 <= j <= n ==> !IsMatchAt(s, t, j);
    } else {
        // n < 0 means |t| < |s|, so no possible match
        assert |t| - |s| < 0;
        // The range 0 <= i <= |t| - |s| is empty when |t| - |s| < 0
        assert forall i :: 0 <= i <= |t| - |s| ==> false;
    }
    return false;
}


// Test cases checked statically.
method IsSublistTest(){
    var a0: seq<int> := [1, 0, 2, 2];
    var a1: seq<int> := [1, 2];
    var a2: seq<int> :=  [0, 2, 2];
    var a3: seq<int> := [];

    // Helper assertions to make verification easier
    assert a0[..] == [1, 0, 2, 2];
    assert a1[..] == [1, 2];
    assert a2[..] == [0, 2, 2];
    assert a3[..] == [];

    var r1 := IsSublist(a1, a0);
    // [1,2] is not a contiguous subsequence of [1,0,2,2]
    // Check all possible positions:
    assert a0[0..2] == [1, 0] != [1, 2];
    assert a0[1..3] == [0, 2] != [1, 2];
    assert a0[2..4] == [2, 2] != [1, 2];
    assert !r1; 

    var r2 := IsSublist(a2, a0);
    // [0,2,2] is a contiguous subsequence starting at index 1
    assert a0[1..4] == [0, 2, 2];
    assert r2; 

    var r3 := IsSublist(a3, a0);
    // Empty sequence is a subsequence of any sequence
    // For empty s, |s| = 0, so i can be 0 <= i <= |t| - 0 = |t|
    // and t[i..i+0] == [] == s for any i in range
    assert r3;

    var r4 := IsSublist(a3, a3);
    // Empty sequence is a subsequence of empty sequence
    assert r4;
}


