// Checks if an array contains at least two consecutive numbers
predicate HasConsecutive(a: array<int>)
  reads a
{
  exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1]
}

method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
  ensures result <==> HasConsecutive(a)
{
    result := false;
    if a.Length > 0 {
        for i := 0 to a.Length - 1
          invariant !result ==> (forall k :: 0 <= k < i ==> a[k] + 1 != a[k + 1])
          invariant result ==> (exists k :: 0 <= k < i && a[k] + 1 == a[k + 1])
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
