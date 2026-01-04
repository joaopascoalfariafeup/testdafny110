// Rotates a list to the right by n positions.
method RotateRight(l: seq<int>, n: nat) returns (r: seq<int>)
    ensures |r| == |l|
    ensures |l| == 0 ==> r == []
    ensures |l| > 0 ==> forall i :: 0 <= i < |l| ==> r[i] == l[(i - n) % |l|]
{
    r := [];
    for i := 0 to |l|
        invariant 0 <= i <= |l|
        invariant |r| == i
        invariant |l| == 0 ==> r == []
        invariant |l| > 0 ==> forall j :: 0 <= j < i ==> r[j] == l[(j - n) % |l|]
    {
        r := r + [l[(i - n) % |l|]];
    }
}

// Test cases checked statically.
method RotateRightTest(){
    var res1 := RotateRight([1, 2, 3, 4, 5], 3);
    assert res1 == [3, 4, 5, 1, 2];

    var res2 := RotateRight([1 , 2, 3, 4, 5], 5);
    assert res2 == [1, 2, 3, 4, 5];

    var res3 := RotateRight([1], 100);
    assert res3 == [1];

    var res4 := RotateRight([], 100);
    assert res4 == [];
}
