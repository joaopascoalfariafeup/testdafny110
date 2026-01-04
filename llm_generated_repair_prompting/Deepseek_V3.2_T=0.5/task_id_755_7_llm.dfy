
// Obtains the smallest and second smallest element in an array of integers (in a single scan).
// The array must have at least two distinct elements.
method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
  requires s.Length >= 2
  requires exists i, j :: 0 <= i < j < s.Length && s[i] != s[j]
  ensures smallest in s[..]
  ensures secondSmallest in s[..]
  ensures forall k :: 0 <= k < s.Length ==> smallest <= s[k]
  ensures exists k :: 0 <= k < s.Length && s[k] == smallest
  ensures exists k :: 0 <= k < s.Length && s[k] == secondSmallest
  ensures smallest < secondSmallest
  ensures forall k :: 0 <= k < s.Length && s[k] != smallest ==> secondSmallest <= s[k]
{
    // index of the smallest element inspected so far.
    var minIndex := 0; 

    // or -1 if all elements are equal so far.
    var secondMinIndex := -1; 

    for i := 1 to s.Length
      invariant 0 <= minIndex < i
      invariant secondMinIndex == -1 || 0 <= secondMinIndex < i
      invariant forall k :: 0 <= k < i ==> s[minIndex] <= s[k]
      invariant secondMinIndex != -1 ==> s[minIndex] < s[secondMinIndex]
      invariant secondMinIndex != -1 ==> forall k :: 0 <= k < i && s[k] != s[minIndex] ==> s[secondMinIndex] <= s[k]
      invariant secondMinIndex == -1 ==> forall k :: 0 <= k < i ==> s[k] == s[minIndex]
      invariant secondMinIndex != -1 ==> (exists k :: 0 <= k < i && s[k] == s[secondMinIndex])
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if secondMinIndex == -1 && s[i] > s[minIndex] {
            secondMinIndex := i;
        } else if secondMinIndex != -1 && s[i] > s[minIndex] && s[i] < s[secondMinIndex] {
            secondMinIndex := i;
        }
    }

    // Postcondition guarantees
    // We need to prove that secondMinIndex is not -1 at the end
    // because the precondition guarantees there are two distinct elements
    assert secondMinIndex != -1 by {
        // Use the precondition to show there must be two distinct elements
        var i, j :| 0 <= i < j < s.Length && s[i] != s[j];
        // At least one of them is different from s[minIndex]
        if s[i] != s[minIndex] {
            // Then by the loop invariant, secondMinIndex cannot be -1
            // The loop invariant says: if secondMinIndex == -1 then all elements are equal to s[minIndex]
            // But s[i] != s[minIndex], contradiction
            // Actually, we need to show that i < s.Length, which is true
            // The loop invariant at the end (i = s.Length) says:
            // secondMinIndex == -1 ==> forall k :: 0 <= k < s.Length ==> s[k] == s[minIndex]
            // But s[i] != s[minIndex], so this cannot hold
            // Therefore secondMinIndex != -1
        } else {
            // Then s[j] != s[minIndex] because s[i] == s[minIndex] and s[i] != s[j]
            // Similarly contradiction
        }
    }
    smallest := s[minIndex];
    secondSmallest := s[secondMinIndex];
}

// Test cases checked statically.
method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -8];
    // Prove precondition: at least two distinct elements
    assert a1[0] != a1[2]; // 1 != -8
    var s1, out1 := SecondSmallest(a1);
    // Add helper assertions to help Dafny verify the test
    assert a1[..] == [1, 2, -8, -2, -2, -8];
    // Let's trace through the algorithm manually to understand
    // minIndex starts at 0 (value 1)
    // i=1: s[1]=2 > 1, secondMinIndex becomes 1 (value 2)
    // i=2: s[2]=-8 < 1, secondMinIndex becomes 0 (value 1), minIndex becomes 2 (value -8)
    // i=3: s[3]=-2 > -8, -2 < 1, so secondMinIndex becomes 3 (value -2)
    // i=4: s[4]=-2 = -2, no change
    // i=5: s[5]=-8 = -8, no change
    // So smallest = -8, secondSmallest = -2
    // Add more detailed assertions to help Dafny
    // First prove that -8 is indeed the smallest
    assert forall k :: 0 <= k < a1.Length ==> -8 <= a1[k];
    // Then prove that -2 is the second smallest
    assert forall k :: 0 <= k < a1.Length && a1[k] != -8 ==> -2 <= a1[k];
    // And that -2 is in the array
    assert -2 in a1[..];
    // And that -8 < -2
    assert -8 < -2;
    // Now the test assertions should hold
    assert s1 == -8;
    assert out1 == -2;
    assert s1 == -8 && out1 == -2;

    var a2:= new int[] [2, 2, 1];
    assert a2[0] != a2[2]; // 2 != 1
    var s2, out2 := SecondSmallest(a2);
    assert a2[..] == [2, 2, 1];
    // Trace: minIndex=0 (2), i=1: s[1]=2=2, i=2: s[2]=1<2, secondMinIndex becomes 0 (2), minIndex becomes 2 (1)
    // Helper assertions
    assert forall k :: 0 <= k < a2.Length ==> 1 <= a2[k];
    assert forall k :: 0 <= k < a2.Length && a2[k] != 1 ==> 2 <= a2[k];
    assert 2 in a2[..];
    assert 1 < 2;
    assert s2 == 1 && out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3[1] != a3[0]; // -3 != -2
    var s3, out3 := SecondSmallest(a3);
    assert a3[..] == [-2, -3, -1];
    // Trace: minIndex=0 (-2), i=1: s[1]=-3 < -2, secondMinIndex becomes 0 (-2), minIndex becomes 1 (-3)
    // i=2: s[2]=-1 > -3, -1 < -2? No, -1 > -2, so secondMinIndex stays 0 (-2)
    // Helper assertions
    assert forall k :: 0 <= k < a3.Length ==> -3 <= a3[k];
    assert forall k :: 0 <= k < a3.Length && a3[k] != -3 ==> -2 <= a3[k];
    assert -2 in a3[..];
    assert -3 < -2;
    assert s3 == -3 && out3 == -2;
}






