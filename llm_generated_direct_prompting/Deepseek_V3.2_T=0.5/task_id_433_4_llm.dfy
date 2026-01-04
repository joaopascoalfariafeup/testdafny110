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
            result := false;
            return;
        }
        i := i + 1;
    }
    result := true;
}

// Test cases checked statically
method IsGreaterTest(){
    var a1 := new int[] [3, 2, 1, 5, 2];
    var out1 := IsGreater(4, a1);
    assert ! out1;

    var out2 := IsGreater(6, a1);
    assert out2;
}
