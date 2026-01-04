// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures |oddList| <= arr.Length
  ensures forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
  ensures forall k :: 0 <= k < arr.Length && IsOdd(arr[k]) ==> arr[k] in oddList
  ensures forall k, l :: 0 <= k < l < arr.Length && IsOdd(arr[k]) && IsOdd(arr[l]) ==> 
    exists idx_k, idx_l :: 0 <= idx_k < idx_l < |oddList| && oddList[idx_k] == arr[k] && oddList[idx_l] == arr[l]
{
  oddList := [];
  for i := 0 to arr.Length
    invariant |oddList| <= i
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in oddList
    invariant forall k, l :: 0 <= k < l < i && IsOdd(arr[k]) && IsOdd(arr[l]) ==> 
      exists idx_k, idx_l :: 0 <= idx_k < idx_l < |oddList| && oddList[idx_k] == arr[k] && oddList[idx_l] == arr[l]
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

