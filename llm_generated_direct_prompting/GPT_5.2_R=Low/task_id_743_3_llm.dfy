// Rotates a list to the right by n positions.
function RotateRightSeq(l: seq<int>, n: nat): seq<int>
{
    if |l| == 0 then []
    else (seq i | 0 <= i < |l| :: l[(i - n) % |l|])
}

method RotateRight(l: seq<int>, n: nat) returns (r: seq<int>)
    ensures r == RotateRightSeq(l, n)
    ensures |r| == |l|
{
    r := [];
    for i := 0 to |l|
        invariant 0 <= i <= |l|
        invariant |r| == i
        invariant (|l| == 0 ==> r == [])
        invariant (|l| > 0 ==> r == (seq j | 0 <= j < i :: l[(j - n) % |l|]))
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
