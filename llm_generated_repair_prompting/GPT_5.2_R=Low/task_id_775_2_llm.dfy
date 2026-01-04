// Checks if all elements at odd indices are odd.
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i])))
{
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a[j]))
    {
        if IsOdd(i) && !IsOdd(a[i]) {
            assert !(forall k :: 0 <= k < a.Length ==> (IsOdd(k) ==> IsOdd(a[k])));
            return false;
        }
    }
    return true;
}

predicate IsOdd(n: int) {
    n % 2 == 1
}

// Test cases checked statically.
method IsOddAtIndexOddTest(){
  var a1 := new int[] [2, 1, 4, 3, 6, 7, 6, 3];
  var out1 := IsOddAtIndexOdd(a1);
  assert out1;

  var a2 := new int[] [1, 2, 3];
  var out2 := IsOddAtIndexOdd(a2);

  // Help Dafny connect the postcondition to this concrete counterexample at index 1
  assert a2[..] == [1, 2, 3];
  assert IsOdd(1);
  assert a2[1] == 2;
  assert !IsOdd(a2[1]);

  // From the method postcondition: out2 ==> forall i ... (instantiate at i = 1)
  assert out2 ==> (forall i :: 0 <= i < a2.Length ==> (IsOdd(i) ==> IsOdd(a2[i])));
  assert out2 ==> (IsOdd(1) ==> IsOdd(a2[1]));
  assert out2 ==> IsOdd(a2[1]);
  assert out2 ==> false;

  assert !out2;
}
