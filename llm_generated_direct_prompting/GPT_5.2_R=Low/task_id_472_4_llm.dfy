predicate HasConsecutive(s: seq<int>)
{
    exists i :: 0 <= i < |s| - 1 && s[i] + 1 == s[i + 1]
}

// Checks if an array contains at least two consecutive numbers
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    ensures result <==> HasConsecutive(a[..])
{
    result := false;
    if a.Length > 0 {
        for i := 0 to a.Length - 1
            invariant 0 <= i <= a.Length - 1
            invariant !result ==> (forall j :: 0 <= j < i ==> a[j] + 1 != a[j + 1])
            invariant result ==> (exists j :: 0 <= j <= i && j < a.Length - 1 && a[j] + 1 == a[j + 1])
        {
            if a[i] + 1 == a[i + 1] {
                result := true;
                break;
            }
        }
        if !result {
            assert forall j :: 0 <= j < a.Length - 1 ==> a[j] + 1 != a[j + 1];
        } else {
            assert exists j :: 0 <= j < a.Length - 1 && a[j] + 1 == a[j + 1];
        }
    }
}

// Test cases checked statically
method ContainsConsecutiveNumbersTest(){
    // all consecutive
    var a1 := new int[] [1, 2, 3, 4, 5];
    var out1 := ContainsConsecutiveNumbers(a1);
    assert out1;

    // some consecutive
    var a2 := new int[] [1, 3, 4, 6];
    var out2 := ContainsConsecutiveNumbers(a2);
    assert out2;

    // none consecutive
    var a3 := new int[] [1, 3, 5];
    var out3 := ContainsConsecutiveNumbers(a3);
    assert !out3;
}
