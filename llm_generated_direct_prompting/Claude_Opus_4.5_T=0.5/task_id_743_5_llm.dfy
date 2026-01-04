// Helper function to compute modulo that always returns non-negative result
ghost function Mod(a: int, b: nat): nat
    requires b > 0
{
    ((a % b) + b) % b
}

// Rotates a list to the right by n positions.
method RotateRight(l: seq<int>, n: nat) returns (r: seq<int>)
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[Mod(i - n, |l|)]
    ensures |l| == 0 ==> r == []
{
    r := [];
    for i := 0 to |l|
        invariant |r| == i
        invariant forall j :: 0 <= j < i ==> r[j] == l[Mod(j - n, |l|)]
    {
        r := r + [l[(i - n) % |l|]];
    }
}

// Test cases checked statically.
method RotateRightTest(){
    var res1 := RotateRight([1, 2, 3, 4, 5], 3);
    assert Mod(0 - 3, 5) == 2;
    assert Mod(1 - 3, 5) == 3;
    assert Mod(2 - 3, 5) == 4;
    assert Mod(3 - 3, 5) == 0;
    assert Mod(4 - 3, 5) == 1;
    assert res1 == [3, 4, 5, 1, 2];

    var res2 := RotateRight([1 , 2, 3, 4, 5], 5);
    assert Mod(0 - 5, 5) == 0;
    assert Mod(1 - 5, 5) == 1;
    assert Mod(2 - 5, 5) == 2;
    assert Mod(3 - 5, 5) == 3;
    assert Mod(4 - 5, 5) == 4;
    assert res2 == [1, 2, 3, 4, 5];

    var res3 := RotateRight([1], 100);
    assert Mod(0 - 100, 1) == 0;
    assert res3 == [1];

    var res4 := RotateRight([], 100);
    assert res4 == [];
}
