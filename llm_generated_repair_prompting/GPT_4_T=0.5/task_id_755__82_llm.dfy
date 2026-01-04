predicate distinctElements(s: array<int>)
    reads s
{
    forall i, j :: 0 <= i < j < s.Length ==> s[i] != s[j]
}

method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
    requires s.Length > 1
    requires distinctElements(s)
    ensures forall i :: 0 <= i < s.Length ==> s[i] >= smallest
    ensures exists i :: 0 <= i < s.Length && s[i] == smallest
    ensures forall i :: 0 <= i < s.Length ==> s[i] == smallest || s[i] >= secondSmallest
    ensures exists i :: 0 <= i < s.Length && s[i] == secondSmallest
    ensures smallest < secondSmallest // changed from <= to <
{
    var minIndex := 0;
    var secondMinIndex := 1;
    if s[secondMinIndex] < s[minIndex] {
        minIndex := 1;
        secondMinIndex := 0;
    }

    for i := 2 to s.Length
        invariant 2 <= i <= s.Length
        invariant 0 <= minIndex < i
        invariant 0 <= secondMinIndex < i && secondMinIndex != minIndex
        invariant forall j :: 0 <= j < i ==> s[j] >= s[minIndex]
        invariant exists j :: 0 <= j < i && s[j] == s[minIndex]
        invariant forall j :: 0 <= j < i ==> s[j] == s[minIndex] || s[j] >= s[secondMinIndex]
        invariant exists j :: 0 <= j < i && s[j] == s[secondMinIndex]
        invariant s[minIndex] < s[secondMinIndex] // added this invariant
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] > s[minIndex] && s[i] < s[secondMinIndex] {
            secondMinIndex := i;
        }
    }

    return s[minIndex], s[secondMinIndex];
}

method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -1];
    assert a1.Length > 1;
    assert distinctElements(a1);
    var s1, out1 := SecondSmallest(a1);
    assert  s1 == -8 && out1 == -2;

    var a2:= new int[] [2, 3, 1];
    assert a2.Length > 1;
    assert distinctElements(a2);
    var s2, out2 := SecondSmallest(a2);
    assert s2 == 1 && out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3.Length > 1;
    assert distinctElements(a3);
    var s3, out3 := SecondSmallest(a3);
    assert s3 == -3 && out3 == -2;
}
