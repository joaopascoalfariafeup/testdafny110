// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures |oddList| <= arr.Length
  ensures forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
  ensures forall k :: 0 <= k < arr.Length && IsOdd(arr[k]) ==> arr[k] in oddList
  ensures forall k :: 0 <= k < |oddList| ==> exists j :: 0 <= j < arr.Length && arr[j] == oddList[k] && IsOdd(arr[j])
  ensures forall j :: 0 <= j < arr.Length && IsOdd(arr[j]) ==> exists k :: 0 <= k < |oddList| && oddList[k] == arr[j]
{
  oddList := [];
  for i := 0 to arr.Length
    invariant |oddList| <= i
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in oddList
    invariant forall k :: 0 <= k < |oddList| ==> exists j :: 0 <= j < i && arr[j] == oddList[k] && IsOdd(arr[j])
    invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> exists k :: 0 <= k < |oddList| && oddList[k] == arr[j]
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
  assert res1 == [1, 3];

  var a2:= new int[] [1, 3, 5];
  var res2 := FilterOddNumbers(a2);
  assert res2 == [1, 3, 5];

  var a3 := new int[] [2, 4, 6, 8];
  var res3:=FilterOddNumbers(a3);
  assert res3 == [];
}

