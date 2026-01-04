// Returns a list of the elements of the input list raised to the power of n (>=0).
function PowSeq(l: seq<int>, n: nat): seq<int>
{
  if |l| == 0 then []
  else PowSeq(l[..|l|-1], n) + [Power(l[|l|-1], n)]
}

method PowerOfListElements(l: seq<int>, n: nat) returns (result: seq<int>)
  ensures result == PowSeq(l, n)
  ensures |result| == |l|
  ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
  result := [];
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant result == PowSeq(l[..i], n)
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == Power(l[j], n)
  {
    result := result + [Power(l[i], n)];
  }
}

// Returns the base raised to the power of the exponent.
function Power(base: int, exponent: nat): int {
  if exponent == 0 then 1
  else base * Power(base, exponent-1)
}

method PowerOfListElementsTest(){
  var s1: seq<int> := [1, 2, 3, 4];
  var res1:=PowerOfListElements(s1, 2);
  assert res1 == [1, 4, 9, 16];

  var s2: seq<int> := [10, 20, 30];
  var res2:=PowerOfListElements(s2, 3);
  assert res2 == [1000, 8000, 27000];
}

