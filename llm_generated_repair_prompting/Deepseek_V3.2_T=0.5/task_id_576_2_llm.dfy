// Interesting example that previously had a bug for empty lists.
// Checks if a sequence 's' is contained (as a subsequence) in another sequence 't'.
method IsSublist<T(==)>(s: seq<T>, t: seq<T>) returns (result: bool)
  ensures result == exists i :: 0 <= i <= |t| - |s| && s == t[i.. i+|s|]
{
    var n := |t| - |s|;
    if n >= 0 {
        for i := 0 to n + 1
          invariant forall j :: 0 <= j < i ==> s != t[j.. j+|s|]
        {
            if s == t[i.. i+|s|] {
                // Prove postcondition when returning true
                assert 0 <= i <= |t| - |s| && s == t[i.. i+|s|];
                return true;
            }
        }
    }
    // Prove postcondition when returning false
    // Show that no i in range satisfies the condition
    if n >= 0 {
        assert forall j :: 0 <= j <= |t| - |s| ==> s != t[j.. j+|s|];
    } else {
        assert |t| - |s| < 0;
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

    var r1 := IsSublist(a1, a0);
    // [1,2] is not a contiguous subsequence of [1,0,2,2]
    assert !r1; 

    var r2 := IsSublist(a2, a0);
    // [0,2,2] is a contiguous subsequence starting at index 1
    assert r2; 

    var r3 := IsSublist(a3, a0);
    // Empty sequence is a subsequence of any sequence
    assert r3;

    var r4 := IsSublist(a3, a3);
    // Empty sequence is a subsequence of empty sequence
    assert r4;
}

