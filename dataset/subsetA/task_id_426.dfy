// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == Filter(arr[..], IsOdd)
{
  oddList := [];
  for i := 0 to arr.Length
    invariant oddList == Filter(arr[..i], IsOdd)
  {
    assert arr[..i+1] == arr[..i] + [arr[i]]; // proof helper
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
    }
  }
  assert arr[..] == arr[..arr.Length]; // proof helper
}

// Auxiliary predicate to checks if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Select from a sequence 'a' the elements that satisfy a predicate 'p'.
ghost function {:fuel 4} Filter<T>(a: seq<T>, p: (T) -> bool): seq<T> {
  if |a| == 0 then []
  else if p(a[|a|-1]) then Filter(a[..|a|-1], p) + [a[|a|-1]]
  else Filter(a[..|a|-1], p)
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
