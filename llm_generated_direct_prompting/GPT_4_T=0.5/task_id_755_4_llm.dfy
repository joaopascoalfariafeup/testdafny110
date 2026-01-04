
// Obtains the smallest and second smallest element in an array of integers (in a single scan).
// The array must have at least two distinct elements.
method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
    requires s.Length > 1
    requires exists i, j :: 0 <= i < j < s.Length && s[i] != s[j] // There are at least two distinct elements in the array
    ensures forall i :: 0 <= i < s.Length ==> s[i] >= smallest
    ensures forall i :: 0 <= i < s.Length ==> s[i] >= secondSmallest
    ensures smallest < secondSmallest || (smallest == secondSmallest && forall i :: 0 <= i < s.Length ==> s[i] == smallest)
{
    // index of the smallest element inspected so far.
    var minIndex := 0; 

    // or -1 if all elements are equal so far.
    var secondMinIndex := -1; 

    for i := 1 to s.Length
        invariant 0 <= minIndex < i
        invariant secondMinIndex == -1 || (0 <= secondMinIndex < i && secondMinIndex != minIndex)
        invariant forall j :: 0 <= j < i ==> s[j] >= s[minIndex]
        invariant secondMinIndex == -1 || forall j :: 0 <= j < i ==> s[j] >= s[secondMinIndex]
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] > s[minIndex] && (secondMinIndex == -1 || s[i] < s[secondMinIndex]) {
            secondMinIndex := i;
        }
    }

    return s[minIndex], s[secondMinIndex];
}

// Test cases checked statically.
method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -8];
    var s1, out1 := SecondSmallest(a1);
    assert  s1 == -8 && out1 == -2;

    var a2:= new int[] [2, 2, 1];
    assert a2[0] != a2[2];
    var s2, out2 := SecondSmallest(a2);
    assert s2 == 1 && out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3[1] != a3[0];
    var s3, out3 := SecondSmallest(a3);
    assert s3 == -3 && out3 == -2;
}
