// Checks if a number 'n' is greater than all elements in an array 'a'
method IsGreater(n: int, a: array<int>) returns (result: bool)
  ensures result == (forall k :: 0 <= k < a.Length ==> n > a[k])
{
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> n > a[k]
    {
        if n <= a[i] {
            return false;
        }
        i := i + 1;
    }
    return true;
}

// Test cases checked statically
method IsGreaterTest(){
    var a1 := new int[] [3, 2, 1, 5, 2];
    // Add helper assertion to help Dafny understand array contents
    assert a1[0] == 3 && a1[1] == 2 && a1[2] == 1 && a1[3] == 5 && a1[4] == 2;
    var out1 := IsGreater(4, a1);
    // 4 is not greater than 5 (a1[3] == 5), so result should be false
    assert ! out1;

    var out2 := IsGreater(6, a1);
    // 6 is greater than all elements [3, 2, 1, 5, 2], so result should be true
    assert out2;
}

