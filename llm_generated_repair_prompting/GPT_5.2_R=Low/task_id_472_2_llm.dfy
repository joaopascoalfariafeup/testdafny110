ghost predicate ConsecutiveAt(a: array<int>, i: int)
  requires a != null
  requires 0 <= i < a.Length - 1
  reads a
{
  a[i] + 1 == a[i + 1]
}

// Checks if an array contains at least two consecutive numbers
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a != null
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
{
    result := false;
    if a.Length > 0 {
        for i := 0 to a.Length - 1
            invariant 0 <= i <= a.Length - 1
            invariant !result ==> (forall j :: 0 <= j < i ==> !ConsecutiveAt(a, j))
            invariant result ==> ((exists j :: 0 <= j < i ==> ConsecutiveAt(a, j)) ||
                                  (i < a.Length - 1 && ConsecutiveAt(a, i)))
        {
            if a[i] + 1 == a[i + 1] {
                // Help the verifier connect the raw array expression to ConsecutiveAt
                assert 0 <= i < a.Length - 1;
                assert ConsecutiveAt(a, i);
                result := true;
                assert exists j :: 0 <= j < i + 1 && a[j] + 1 == a[j + 1];
                break;
            }
        }
    }
}

// Test cases checked statically
method ContainsConsecutiveNumbersTest(){
    // all consecutive
    var a1 := new int[] [1, 2, 3, 4, 5];
    assert a1[..] == [1, 2, 3, 4, 5];
    var out1 := ContainsConsecutiveNumbers(a1);
    assert out1;

    // some consecutive
    var a2 := new int[] [1, 3, 4, 6];
    assert a2[..] == [1, 3, 4, 6];
    var out2 := ContainsConsecutiveNumbers(a2);
    assert out2;

    // none consecutive
    var a3 := new int[] [1, 3, 5];
    assert a3[..] == [1, 3, 5];
    var out3 := ContainsConsecutiveNumbers(a3);
    assert !out3;
}
