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
  var indexMap: seq<int> := []; // ghost variable to track indices
  for i := 0 to arr.Length
    invariant |oddList| <= i
    invariant |oddList| == |indexMap|
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in oddList
    invariant forall k :: 0 <= k < |oddList| ==> 
      0 <= indexMap[k] < i && arr[indexMap[k]] == oddList[k] && IsOdd(arr[indexMap[k]])
    // Additional invariant to preserve order
    invariant forall k, l :: 0 <= k < l < |oddList| ==> indexMap[k] < indexMap[l]
  {
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
      indexMap := indexMap + [i];
    }
  }
}

// Auxiliary predicate to checks if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Helper lemma to prove test assertions
lemma TestHelper(arr: array<int>, oddList: seq<int>)
  requires arr.Length >= 0
  requires forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
  requires forall k :: 0 <= k < arr.Length && IsOdd(arr[k]) ==> arr[k] in oddList
  requires forall k :: 0 <= k < |oddList| ==> exists j :: 0 <= j < arr.Length && arr[j] == oddList[k] && IsOdd(arr[j])
  requires forall k, l :: 0 <= k < l < |oddList| ==> 
    exists i, j :: 0 <= i < j < arr.Length && arr[i] == oddList[k] && arr[j] == oddList[l] && IsOdd(arr[i]) && IsOdd(arr[j])
{
  // This lemma helps trigger verification for test cases
}

// Test cases checked statically.
method FilterOddNumbersTest(){
  var a1:= new int[] [1, 2, 3, 4];
  var res1 := FilterOddNumbers(a1);
  // Add helper assertions
  assert a1[..] == [1, 2, 3, 4];
  assert IsOdd(a1[0]) && IsOdd(a1[2]);
  assert !IsOdd(a1[1]) && !IsOdd(a1[3]);
  // Call helper lemma to establish postconditions
  TestHelper(a1, res1);
  // Prove res1 == [1, 3] by checking each element
  assert |res1| == 2;
  assert res1[0] == 1;
  assert res1[1] == 3;
  assert res1 == [1, 3];

  var a2:= new int[] [1, 3, 5];
  var res2 := FilterOddNumbers(a2);
  // Add helper assertions
  assert a2[..] == [1, 3, 5];
  assert IsOdd(a2[0]) && IsOdd(a2[1]) && IsOdd(a2[2]);
  // Call helper lemma to establish postconditions
  TestHelper(a2, res2);
  // Prove res2 == [1, 3, 5] by checking each element
  assert |res2| == 3;
  assert res2[0] == 1;
  assert res2[1] == 3;
  assert res2[2] == 5;
  assert res2 == [1, 3, 5];

  var a3 := new int[] [2, 4, 6, 8];
  var res3:=FilterOddNumbers(a3);
  // Add helper assertions
  assert a3[..] == [2, 4, 6, 8];
  assert !IsOdd(a3[0]) && !IsOdd(a3[1]) && !IsOdd(a3[2]) && !IsOdd(a3[3]);
  // Call helper lemma to establish postconditions
  TestHelper(a3, res3);
  // Prove res3 == [] by checking length
  assert |res3| == 0;
  assert res3 == [];
}










