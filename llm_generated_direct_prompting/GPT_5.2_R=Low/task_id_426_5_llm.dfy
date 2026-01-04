// Returns a sequence with the odd numbers in the input array, by the same order.
function FilterOdd(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then
    []
  else if IsOdd(s[|s| - 1]) then
    FilterOdd(s[..|s| - 1]) + [s[|s| - 1]]
  else
    FilterOdd(s[..|s| - 1])
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == FilterOdd(arr[..])
{
  oddList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant oddList == FilterOdd(arr[..i])
  {
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
      assert FilterOdd(arr[..i+1]) == FilterOdd(arr[..i]) + [arr[i]];
      assert oddList == FilterOdd(arr[..i+1]);
    } else {
      assert FilterOdd(arr[..i+1]) == FilterOdd(arr[..i]);
      assert oddList == FilterOdd(arr[..i+1]);
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

