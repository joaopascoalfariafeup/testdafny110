// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == FilterOddSeq(arr[..])
{
  oddList := [];
  for i := 0 to arr.Length
    invariant oddList == FilterOddSeq(arr[..i])
  {
    assert arr[..i+1] == arr[..i] + [arr[i]];
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
    }
  }
  assert arr[..arr.Length] == arr[..];
}

// Auxiliary predicate to checks if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Auxiliary ghost function to filter odd numbers from a sequence
ghost function {:fuel 5} FilterOddSeq(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if IsOdd(s[0]) then [s[0]] + FilterOddSeq(s[1..])
  else FilterOddSeq(s[1..])
}

// Lemma to help prove the append property
lemma FilterOddSeqAppend(s: seq<int>, x: int)
  ensures FilterOddSeq(s + [x]) == FilterOddSeq(s) + (if IsOdd(x) then [x] else [])
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    FilterOddSeqAppend(s[1..], x);
  }
}

// Test cases checked statically.
method FilterOddNumbersTest(){
  var a1:= new int[] [1, 2, 3, 4];
  var res1 := FilterOddNumbers(a1);
  assert a1[..] == [1, 2, 3, 4];
  assert res1 == [1, 3];

  var a2:= new int[] [1, 3, 5];
  var res2 := FilterOddNumbers(a2);
  assert a2[..] == [1, 3, 5];
  assert res2 == [1, 3, 5];

  var a3 := new int[] [2, 4, 6, 8];
  var res3:=FilterOddNumbers(a3);
  assert a3[..] == [2, 4, 6, 8];
  assert res3 == [];
}
