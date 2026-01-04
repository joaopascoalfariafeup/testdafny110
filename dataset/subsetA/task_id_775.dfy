// Checks if all elements at odd indices are odd.
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length && IsOdd(i) ==> IsOdd(a[i])
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
  assert a2[1] == 2; // proof helper (counter example)
  assert !out2;
}