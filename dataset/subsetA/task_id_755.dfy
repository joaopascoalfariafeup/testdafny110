
// Obtains the smallest and second smallest element in an array of integers (in a single scan).
// The array must have at least two distinct elements.
method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
    requires exists i, j :: 0 <= i < j < s.Length && s[i] != s[j]
    ensures smallest in s[..]
    ensures forall k :: 0 <= k < s.Length ==> s[k] >= smallest 
    ensures secondSmallest in s[..] && secondSmallest > smallest
    ensures forall k :: 0 <= k < s.Length && s[k] != smallest ==> s[k] >= secondSmallest 
{
    // index of the smallest element inspected so far.
    var minIndex := 0; 

    // or -1 if all elements are equal so far.
    var secondMinIndex := -1; 

    for i := 1 to s.Length
      invariant 0 <= minIndex < i
      invariant -1 <= secondMinIndex < i
      invariant secondMinIndex != -1 ==> s[secondMinIndex] > s[minIndex]
      invariant forall k :: 0 <= k < i ==> s[k] == s[minIndex] || (secondMinIndex != -1 && s[k] >= s[secondMinIndex])
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
    assert a1[2] != a1[3]; // proof helper (example for precondition)
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