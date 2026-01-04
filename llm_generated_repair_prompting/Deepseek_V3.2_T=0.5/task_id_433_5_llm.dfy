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
    
    // Additional helper: explicitly show that 4 is not greater than a1[3]
    assert 0 <= 3 < a1.Length && 4 <= a1[3];
    // This implies: exists k :: 0 <= k < a1.Length && 4 <= a1[k]
    // Therefore: !(forall k :: 0 <= k < a1.Length ==> 4 > a1[k])
    
    var out1 := IsGreater(4, a1);
    // 4 is not greater than 5 (a1[3] == 5), so result should be false
    // Add explicit proof that out1 must be false
    // From the postcondition of IsGreater: out1 == (forall k :: 0 <= k < a1.Length ==> 4 > a1[k])
    // We know a1[3] == 5 and 4 <= 5, so the forall is false
    assert !(forall k :: 0 <= k < a1.Length ==> 4 > a1[k]) by {
        assert 0 <= 3 < a1.Length;
        assert 4 <= a1[3];
    }
    assert ! out1;

    var out2 := IsGreater(6, a1);
    // 6 is greater than all elements [3, 2, 1, 5, 2], so result should be true
    // Add explicit proof that out2 must be true
    assert (forall k :: 0 <= k < a1.Length ==> 6 > a1[k]) by {
        assert a1[0] == 3 && 6 > 3;
        assert a1[1] == 2 && 6 > 2;
        assert a1[2] == 1 && 6 > 1;
        assert a1[3] == 5 && 6 > 5;
        assert a1[4] == 2 && 6 > 2;
    }
    assert out2;
}

