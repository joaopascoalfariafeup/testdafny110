// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures forall k :: 0 <= k < |res| ==> res[k] < 0
  ensures forall k :: 0 <= k < a.Length && a[k] < 0 ==> res[SeqCount(res, a[k])] == a[k]
  ensures forall k, v :: 0 <= k < |res| && res[k] == v ==> SeqCount(a, v) == SeqCount(res, v)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == [j in a[..i] | j < 0]
    invariant forall k :: 0 <= k < i && a[k] < 0 ==> res[SeqCount(res, a[k])] == a[k]
    invariant forall k, v :: 0 <= k < |res| && res[k] == v ==> SeqCount(a[..i], v) == SeqCount(res, v)
  {
    if a[i] < 0 {
      res := res + [a[i]];
    }
  }
}

// Auxiliary function to count the number of times a value appears in a sequence
function SeqCount(s: seq<int>, v: int): int
{
  if |s| == 0 then 0 else (if s[|s|-1] == v then 1 else 0) + SeqCount(s[..|s|-1], v)
}

// Test cases checked statically.
method FindNegativeNumbersTest(){
  var a1 := new int[] [-1, 4, 5, -6];
  var res1 := FindNegativeNumbers(a1);
  assert res1 == [-1, -6];

  var a2:= new int[] [-1, -2, -3];
  var res2 := FindNegativeNumbers(a2);
  assert res2 == [-1, -2, -3];

  var a3:= new int[] [0, 1];
  var res3 := FindNegativeNumbers(a3);
  assert res3 == [];
}
