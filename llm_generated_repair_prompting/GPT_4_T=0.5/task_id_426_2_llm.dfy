// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i])
    ensures forall i, j :: 0 <= i < j < arr.Length && IsOdd(arr[i]) && IsOdd(arr[j]) && arr[i] in oddList && arr[j] in oddList ==> IndexOf(oddList, arr[i]) < IndexOf(oddList, arr[j])
{
  oddList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) && arr[k] in oddList ==> oddList[IndexOf(oddList, arr[k])] == arr[k]
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) && arr[k] in oddList ==> IndexOf(oddList, arr[k]) < |oddList|
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

// Auxiliary function to get the index of a value in a sequence
function IndexOf(s: seq<int>, val: int): int
  requires val in s
  decreases |s|
{
  if s[0] == val then 0 else 1 + IndexOf(s[1..], val)
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
