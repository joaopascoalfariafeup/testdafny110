// Checks if all elements at odd indices are odd.
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
  ensures result <==> forall k :: 0 <= k < a.Length && IsOdd(k) ==> IsOdd(a[k])
{
    for i := 0 to a.Length
      invariant forall k :: 0 <= k < i && IsOdd(k) ==> IsOdd(a[k])
    {
        if IsOdd(i) && !IsOdd(a[i]) {
            assert IsOdd(i) && !IsOdd(a[i]);
            assert 0 <= i < a.Length && IsOdd(i) && !IsOdd(a[i]);
            assert !(forall k :: 0 <= k < a.Length && IsOdd(k) ==> IsOdd(a[k]));
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
  assert a2[..] == [1, 2, 3];  // helper assertion
  assert a2[1] == 2;  // helper assertion
  assert IsOdd(1) && !IsOdd(2);  // helper: index 1 is odd, value 2 is even
  assert 0 <= 1 < a2.Length && IsOdd(1) && !IsOdd(a2[1]);  // witness for negation
  var out2 := IsOddAtIndexOdd(a2);
  // After the call, use the postcondition and the witness to prove !out2
  assert a2[1] == 2;  // re-establish after call
  assert IsOdd(1);  // index 1 is odd
  assert !IsOdd(a2[1]);  // value at index 1 is not odd
  assert 0 <= 1 < a2.Length;  // index 1 is in bounds
  assert !(0 <= 1 < a2.Length && IsOdd(1) ==> IsOdd(a2[1]));  // the implication is false for k=1
  assert exists k :: 0 <= k < a2.Length && IsOdd(k) && !IsOdd(a2[k]);  // witness exists
  assert !(forall k :: 0 <= k < a2.Length && IsOdd(k) ==> IsOdd(a2[k]));  // negation of forall
  assert !out2;
}
