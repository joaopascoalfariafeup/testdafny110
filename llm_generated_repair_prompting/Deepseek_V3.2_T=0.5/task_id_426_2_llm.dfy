// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures |oddList| <= arr.Length
  ensures forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
  ensures forall k :: 0 <= k < arr.Length && IsOdd(arr[k]) ==> arr[k] in oddList
  ensures forall k :: 0 <= k < |oddList| ==> exists j :: 0 <= j < arr.Length && arr[j] == oddList[k] && IsOdd(arr[j])
  // Additional postcondition to ensure order preservation
  ensures forall k, l :: 0 <= k < l < |oddList| ==> 
    exists i, j :: 0 <= i < j < arr.Length && arr[i] == oddList[k] && arr[j] == oddList[l] && IsOdd(arr[i]) && IsOdd(arr[j])
{
  oddList := [];
  for i := 0 to arr.Length
    invariant |oddList| <= i
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in oddList
    invariant forall k :: 0 <= k < |oddList| ==> exists j :: 0 <= j < i && arr[j] == oddList[k] && IsOdd(arr[j])
    // Additional invariant to preserve order
    invariant forall k, l :: 0 <= k < l < |oddList| ==> 
      exists i1, i2 :: 0 <= i1 < i2 < i && arr[i1] == oddList[k] && arr[i2] == oddList[l] && IsOdd(arr[i1]) && IsOdd(arr[i2])
  {
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
    }
  }
}

// Auxiliary predicate to checks if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}



// Test cases checked statically.
method FilterOddNumbersTest(){
  var a1:= new int[] [1, 2, 3, 4];
  var res1 := FilterOddNumbers(a1);
  // Add helper assertions
  assert a1[..] == [1, 2, 3, 4];
  assert IsOdd(a1[0]) && IsOdd(a1[2]);
  assert !IsOdd(a1[1]) && !IsOdd(a1[3]);
  assert res1 == [1, 3];

  var a2:= new int[] [1, 3, 5];
  var res2 := FilterOddNumbers(a2);
  // Add helper assertions
  assert a2[..] == [1, 3, 5];
  assert IsOdd(a2[0]) && IsOdd(a2[1]) && IsOdd(a2[2]);
  assert res2 == [1, 3, 5];

  var a3 := new int[] [2, 4, 6, 8];
  var res3:=FilterOddNumbers(a3);
  // Add helper assertions
  assert a3[..] == [2, 4, 6, 8];
  assert !IsOdd(a3[0]) && !IsOdd(a3[1]) && !IsOdd(a3[2]) && !IsOdd(a3[3]);
  assert res3 == [];
}


