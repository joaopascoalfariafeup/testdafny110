// Checks if an array contains at least two consecutive numbers
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
{
    result := false;
    if a.Length > 0 {
        for i := 0 to a.Length - 1
            invariant forall k :: 0 <= k < i ==> a[k] + 1 != a[k + 1]
        {
            if a[i] + 1 == a[i + 1] {
                result := true;
                break;
            }
        }
    }
}

// Test cases checked statically
method ContainsConsecutiveNumbersTest(){
    // all consecutive
    var a1 := new int[] [1, 2, 3, 4, 5];
    var out1 := ContainsConsecutiveNumbers(a1);
    assert a1[1] == a1[0] + 1; // proof helper (example)
    assert out1;

    // some consecutive
    var a2 := new int[] [1, 3, 4, 6];
    var out2 := ContainsConsecutiveNumbers(a2);
    assert a2[2] == a2[1] + 1; // proof helper (example)
    assert out2;

    // none consecutive
    var a3 := new int[] [1, 3, 5];
    var out3 := ContainsConsecutiveNumbers(a3);
    assert !out3;

    var a4 := new int[] [1];
    var out4 := ContainsConsecutiveNumbers(a4);
    assert !out4;

    var a5 := new int[] [];
    var out5 := ContainsConsecutiveNumbers(a5);
    assert !out5;
}