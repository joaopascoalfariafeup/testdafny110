// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == FilterOddsSeq(arr[..])
{
  oddList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant oddList == FilterOddsSeq(arr[..i])
  {
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
    }
    assert FilterOddsSeq(arr[..i+1]) == FilterOddsSeq(arr[..i]) + (if IsOdd(arr[i]) then [arr[i]] else []);
  }
}

// Auxiliary predicate to checks if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}

function FilterOddsSeq(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else FilterOddsSeq(s[..|s|-1]) + (if IsOdd(s[|s|-1]) then [s[|s|-1]] else [])
}

lemma FilterOddsExtend(s: seq<int>, x: int)
  ensures FilterOddsSeq(s + [x]) == FilterOddsSeq(s) + (if IsOdd(x) then [x] else [])
{
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

