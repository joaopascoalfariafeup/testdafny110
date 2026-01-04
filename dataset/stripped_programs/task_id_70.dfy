// Checks if all sequences in a list of sequences have the same length.
method AllSequencesEqualLength<T>(list: seq<seq<T>>) returns (result: bool)
{
    if |list| == 0 {
        return true;
    }
    var firstLength := |list[0]|;
    for i := 1 to |list|
    {
        if |list[i]| != firstLength {
            return false;
        }
    }
    return true;
}

method AllSequencesEqualLengthTest(){
    var s1: seq<seq<int>> := [[11, 22, 33], [44, 55, 66]];
    var res1:=AllSequencesEqualLength(s1);
    assert res1;
    
    var s2: seq<seq<int>> :=[[1, 2, 3], [4, 5, 6, 7]];
    var res2:=AllSequencesEqualLength(s2);
    assert !res2;
    
    var s3: seq<seq<int>> :=[[1, 2], [3, 4]];
    var res3 := AllSequencesEqualLength(s3);
    assert res3;
}