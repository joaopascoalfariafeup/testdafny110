// Finds the index of the first odd number in an arrray.
// If there is no odd number, returns -1.
method FindFirstOdd(a: array<int>) returns (index: int)
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> !IsOdd(a[k])
  ensures 0 <= index < a.Length ==> IsOdd(a[index])
  ensures 0 <= index < a.Length ==> forall k :: 0 <= k < index ==> !IsOdd(a[k])
  // Make the result uniquely determined (the first odd if any, otherwise -1)
  ensures index == -1 || (forall j :: 0 <= j < a.Length && IsOdd(a[j]) ==> index <= j)
{
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> !IsOdd(a[k])
  {
    if IsOdd(a[i]) {
      return i;
    }
  }
  return -1;
}

predicate IsOdd(x: int) {
  x % 2 != 0
}

// Test cases checked statically.
method FindFirstOddTest(){
  // first
  var a1 := new int[] [1, 3, 5];
  assert a1[..] == [1, 3, 5];

  var out1 := FindFirstOdd(a1);
  assert IsOdd(a1[0]);
  assert out1 == 0;

  // last
  var a2 := new int[] [2, 4, 1];
  assert a2[..] == [2, 4, 1];

  var out2 := FindFirstOdd(a2);
  assert !IsOdd(a2[0]) && !IsOdd(a2[1]) && IsOdd(a2[2]);
  assert out2 == 2;

  // none
  var a3 := new int[] [2, 6, 4];
  assert a3[..] == [2, 6, 4];

  var out3 := FindFirstOdd(a3);
  assert forall k :: 0 <= k < a3.Length ==> !IsOdd(a3[k]);
  assert out3 == -1;
}
