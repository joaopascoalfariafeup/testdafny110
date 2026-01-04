// Checks if all elements at odd indices are odd.
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
  ensures result <==> (forall k :: 0 <= k < a.Length && IsOdd(k) ==> IsOdd(a[k]))
{
    for i := 0 to a.Length
      invariant forall k :: 0 <= k < i && IsOdd(k) ==> IsOdd(a[k])
    {
        if IsOdd(i) && !IsOdd(a[i]) {
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
  assert out2 == false; // use explicit comparison to false instead of negation

  // Add helper assertions to help Dafny prove the test outcome
  assert a2[0] == 1 && a2[1] == 2 && a2[2] == 3; // helper
  assert IsOdd(a2[0]) && !IsOdd(a2[1]) && IsOdd(a2[2]); // helper
  assert a2.Length == 3; // additional helper to ensure the length of the array
  assert forall k :: 0 <= k < a2.Length && IsOdd(k) ==> IsOdd(a2[k]) == false; // additional helper for the postcondition
}
