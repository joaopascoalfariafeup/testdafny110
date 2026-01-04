// Returns a list of the elements of the input list raised to the power of n (>=0).
function {:fuel 10} PowSeq(l: seq<int>, n: nat): seq<int>
{
  if |l| == 0 then []
  else PowSeq(l[..|l|-1], n) + [Power(l[|l|-1], n)]
}

// A convenient “comprehension” specification of powering each element (in order)
function PowSeqComp(l: seq<int>, n: nat): seq<int>
{
  seq i | 0 <= i < |l| :: Power(l[i], n)
}

lemma PowSeqCompExtend(l: seq<int>, n: nat, i: nat)
  requires i < |l|
  ensures PowSeqComp(l[..i+1], n) == PowSeqComp(l[..i], n) + [Power(l[i], n)]
{
  // Prove by extensionality (same length, same elements)
  var a := PowSeqComp(l[..i+1], n);
  var b := PowSeqComp(l[..i], n) + [Power(l[i], n)];

  assert |a| == i + 1;
  assert |b| == i + 1;

  assert forall k :: 0 <= k < |a| ==> a[k] == b[k] by
  {
    fix k | 0 <= k < |a|
    if k < i {
      // both are Power(l[k], n)
    } else {
      assert k == i;
      // last element is Power(l[i], n) on both sides
    }
  }

  assert a == b;
}

lemma PowSeqEqPowSeqComp(l: seq<int>, n: nat)
  ensures PowSeq(l, n) == PowSeqComp(l, n)
{
  if |l| == 0 {
  } else {
    var i: nat := |l| - 1;
    PowSeqEqPowSeqComp(l[..i], n);
    PowSeqCompExtend(l, n, i);
    // Now both sides satisfy the same “append-last” recurrence
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
