// Rotates a list to the right by n positions.
method RotateRight(l: seq<int>, n: nat) returns (r: seq<int>)
    ensures |r| == |l|
    ensures |l| > 0 ==> forall i :: 0 <= i < |l| ==> r[i] == l[(i - n % |l| + |l|) % |l|]
    ensures |l| == 0 ==> r == []
{
    r := [];
    for i := 0 to |l|
        invariant |r| == i
        invariant forall j :: 0 <= j < i ==> r[j] == l[(j - n % |l| + |l|) % |l|]
    {
        var idx := (i - n % |l| + |l|) % |l|;
        r := r + [l[idx]];
    }
}

// Test cases checked statically.
method RotateRightTest(){
    var res1 := RotateRight([1, 2, 3, 4, 5], 3);
    // Helper assertions for res1
    assert (0 - 3 % 5 + 5) % 5 == 2;
    assert (1 - 3 % 5 + 5) % 5 == 3;
    assert (2 - 3 % 5 + 5) % 5 == 4;
    assert (3 - 3 % 5 + 5) % 5 == 0;
    assert (4 - 3 % 5 + 5) % 5 == 1;
    assert res1[0] == 3 && res1[1] == 4 && res1[2] == 5 && res1[3] == 1 && res1[4] == 2;
    assert res1 == [3, 4, 5, 1, 2];

    var res2 := RotateRight([1 , 2, 3, 4, 5], 5);
    // Helper assertions for res2
    assert 5 % 5 == 0;
    assert (0 - 0 + 5) % 5 == 0;
    assert (1 - 0 + 5) % 5 == 1;
    assert (2 - 0 + 5) % 5 == 2;
    assert (3 - 0 + 5) % 5 == 3;
    assert (4 - 0 + 5) % 5 == 4;
    assert res2[0] == 1 && res2[1] == 2 && res2[2] == 3 && res2[3] == 4 && res2[4] == 5;
    assert res2 == [1, 2, 3, 4, 5];

    var res3 := RotateRight([1], 100);
    // Helper assertions for res3
    assert 100 % 1 == 0;
    assert (0 - 0 + 1) % 1 == 0;
    assert res3[0] == 1;
    assert res3 == [1];

    var res4 := RotateRight([], 100);
    assert res4 == [];
}
