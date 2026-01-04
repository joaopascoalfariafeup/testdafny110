// Auxiliary function to calculate the division of a sequence up to a given index
ghost function DivisionUpTo(a: seq<int>, b: seq<int>, n: int) : seq<int>
{
  [a[i] / b[i] | i in 0..n-1] + [0 | i in n..|a|]
}

// Calculates the element-wise division of two sequences of integers of equal length.
method ElementWiseDivision(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b| && forall i :: 0 <= i < |b| ==> b[i] != 0 // sequences have same length and no zero in the denominator
  ensures result == DivisionUpTo(a, b, |a|)
{
  result := [];
  for i := 0 to |a|
    invariant result == DivisionUpTo(a, b, i)
  {
    result := result + [a[i] / b[i]];
  }
}

method ElementWiseDivisionTest(){
  var s1: seq<int> := [10, 4, 6, 9];
  var s2: seq<int> := [5, 2, 3, 3];
  var res1 := ElementWiseDivision(s1,s2);
  assert res1 == [2, 2, 2, 3];

  var s3: seq<int> := [12, 6, 8, 16];
  var s4: seq<int> := [6, 3, 4, 4];
  var res2 := ElementWiseDivision(s3,s4);
  assert res2 == [2, 2, 2, 4];

  var s5: seq<int> := [20, 14, 36, 18];
  var s6: seq<int> := [5, 7, 6, 9];
  var res3:=ElementWiseDivision(s5,s6);
  assert res3 == [4, 2, 6, 2];
}

