// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
  ensures forall i :: 0 <= i < arr.Length ==> (IsOdd(arr[i]) ==> exists k :: 0 <= k < |oddList| && oddList[k] == arr[i])
  ensures forall k :: 0 <= k < |oddList| ==> exists i :: 0 <= i < arr.Length && oddList[k] == arr[i]
  ensures forall i,j :: 0 <= i < j < arr.Length && IsOdd(arr[i]) && IsOdd(arr[j]) ==>
            (exists ki,kj :: 0 <= ki < kj < |oddList| && oddList[ki] == arr[i] && oddList[kj] == arr[j])
{
  oddList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
    invariant forall t :: 0 <= t < i ==> (IsOdd(arr[t]) ==> exists k :: 0 <= k < |oddList| && oddList[k] == arr[t])
    invariant forall k :: 0 <= k < |oddList| ==> exists t :: 0 <= t < i && oddList[k] == arr[t]
    invariant forall p,q :: 0 <= p < q < i && IsOdd(arr[p]) && IsOdd(arr[q]) ==>
              (exists kp,kq :: 0 <= kp < kq < |oddList| && oddList[kp] == arr[p] && oddList[kq] == arr[q])
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

