// Checks if a sequence 's' of elements of any type T contains a given value 'x' of type T.
method InSeq<T(==)>(s: seq<T>, x: T) returns (result: bool)
    ensures result <==> (exists i:int :: 0 <= i < |s| && s[i] == x)
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result == false
        invariant forall j:int :: 0 <= j < i ==> s[j] != x
    {
        // In a Dafny "for i := 0 to |s|", the body is executed only when i < |s|
        assert 0 <= i < |s|;

        if x == s[i] {
            assert exists j:int :: 0 <= j < |s| && s[j] == x by {
                assert 0 <= i < |s|;
            }
            return true;
        }
    }

    // At loop exit, i == |s|
    assert forall j:int :: 0 <= j < |s| ==> s[j] != x;
    assert !(exists j:int :: 0 <= j < |s| && s[j] == x);
    return false;
}

// Test cases checked statically
method InSeqTest(){
    var s1: seq<seq<int>> := [[2,4,3,5,7], [3,8]];
    var s2: seq<int> := [3,7];
    var res1 := InSeq(s1, s2);
    assert res1 == false;

    var s3: seq<seq<int>> := [[2,4,3,5,7],[4,3]];
    var s4: seq<int> := [4,3];
    assert s3[1] == s4;
    assert exists i:int :: 0 <= i < |s3| && s3[i] == s4;
    var res2 := InSeq(s3,s4);
    assert res2 == true;

    var s5: seq<seq<int>> := [[2,4,3,5,7],[1,0]];
    var s6: seq<int> := [1,6];
    var res3 := InSeq(s5,s6);
    assert res3 == false;
}
