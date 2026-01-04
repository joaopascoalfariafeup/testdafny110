// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == FilterOddsPrefix(arr, arr.Length)
{
  oddList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant oddList == FilterOddsPrefix(arr, i)
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

function FilterOddsPrefix(a: array<int>, n: int): seq<int>
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then
    []
  else
    var s := FilterOddsPrefix(a, n - 1);
    if IsOdd(a[n - 1]) then s + [a[n - 1]] else s
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

