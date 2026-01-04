// Returns a list of the elements of the input list raised to the power of n (>=0).
function {:fuel 10} PowSeq(l: seq<int>, n: nat): seq<int>
{
  if |l| == 0 then []
  else PowSeq(l[..|l|-1], n) + [Power(l[|l|-1], n)]
}

// A convenient “comprehension” specification of powering each element (in order)
// Defined with the same (append-last) recursion shape as PowSeq, to match the loop.
function {:fuel 10} PowSeqComp(l: seq<int>, n: nat): seq<int>
{
  if |l| == 0 then []
  else PowSeqComp(l[..|l|-1], n) + [Power(l[|l|-1], n)]
}

lemma PowSeqCompExtend(l: seq<int>, n: nat, i: nat)
  requires i < |l|
  ensures PowSeqComp(l[..i+1], n) == PowSeqComp(l[..i], n) + [Power(l[i], n)]
{
  var p := l[..i+1];
  assert |p| == i + 1;
  assert |p| > 0;

  // Unfold PowSeqComp on p
  assert PowSeqComp(p, n) == PowSeqComp(p[..|p|-1], n) + [Power(p[|p|-1], n)];

  // Relate slices/indexes of p back to l
  assert p[..|p|-1] == l[..i];
  assert p[|p|-1] == l[i];

  // Conclude
}

lemma PowSeqEqPowSeqComp(l: seq<int>, n: nat)
  ensures PowSeq(l, n) == PowSeqComp(l, n)
{
  if |l| == 0 {
  } else {
    PowSeqEqPowSeqComp(l[..|l|-1], n);
    // Unfold both sides once; the recursive calls are equal by IH
    assert PowSeq(l, n) == PowSeq(l[..|l|-1], n) + [Power(l[|l|-1], n)];
    assert PowSeqComp(l, n) == PowSeqComp(l[..|l|-1], n) + [Power(l[|l|-1], n)];
  }
}

// Returns the base raised to the power of the exponent.
function {:fuel 10} Power(base: int, exponent: nat): int {
  if exponent == 0 then 1
  else base * Power(base, exponent-1)
}

method PowerOfListElements(l: seq<int>, n: nat) returns (result: seq<int>)
  ensures result == PowSeq(l, n)
  ensures |result| == |l|
  ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
  result := [];
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant result == PowSeqComp(l[..i], n)
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == Power(l[j], n)
  {
    // maintain result == PowSeqComp(l[..i+1], n) after appending Power(l[i], n)
    PowSeqCompExtend(l, n, i);

    // Help the verifier connect the assignment with the lemma
    assert result + [Power(l[i], n)] == PowSeqComp(l[..i], n) + [Power(l[i], n)];
    assert PowSeqComp(l[..i+1], n) == PowSeqComp(l[..i], n) + [Power(l[i], n)];

    result := result + [Power(l[i], n)];
  }

  PowSeqEqPowSeqComp(l, n);
  assert result == PowSeq(l, n);
}

method PowerOfListElementsTest(){
  var s1: seq<int> := [1, 2, 3, 4];
  var res1:=PowerOfListElements(s1, 2);
  assert res1 == [1, 4, 9, 16];

  var s2: seq<int> := [10, 20, 30];
  var res2:=PowerOfListElements(s2, 3);
  assert res2 == [1000, 8000, 27000];
}
