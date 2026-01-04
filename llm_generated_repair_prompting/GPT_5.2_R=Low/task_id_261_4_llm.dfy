// Calculates the element-wise division of two sequences of integers of equal length.
function DivPrefix(a: seq<int>, b: seq<int>, n: nat): seq<int>
  requires |a| == |b|
  requires n <= |a|
  requires forall k :: 0 <= k < n ==> b[k] != 0
  ensures |DivPrefix(a,b,n)| == n
  ensures forall k :: 0 <= k < n ==> DivPrefix(a,b,n)[k] == a[k] / b[k]
{
  seq(k | 0 <= k < n :: a[k] / b[k])
}

lemma DivPrefixExtend(a: seq<int>, b: seq<int>, i: nat)
  requires |a| == |b|
  requires i < |a|
  requires forall k :: 0 <= k < i + 1 ==> b[k] != 0
  ensures DivPrefix(a, b, i + 1) == DivPrefix(a, b, i) + [a[i] / b[i]]
{
  // Lengths
  assert |DivPrefix(a, b, i + 1)| == i + 1;
  assert |DivPrefix(a, b, i)| == i;
  assert |DivPrefix(a, b, i) + [a[i] / b[i]]| == i + 1;

  // Pointwise equality
  assert forall k :: 0 <= k < i + 1 ==>
    DivPrefix(a, b, i + 1)[k] == (DivPrefix(a, b, i) + [a[i] / b[i]])[k]
  by
  {
    forall k | 0 <= k < i + 1
      ensures DivPrefix(a, b, i + 1)[k] == (DivPrefix(a, b, i) + [a[i] / b[i]])[k]
    {
      if k < i {
        // both sides are the k-th division
        assert DivPrefix(a, b, i + 1)[k] == a[k] / b[k];
        assert DivPrefix(a, b, i)[k] == a[k] / b[k];
        assert (DivPrefix(a, b, i) + [a[i] / b[i]])[k] == DivPrefix(a, b, i)[k];
      } else {
        assert k == i;
        assert DivPrefix(a, b, i + 1)[k] == a[k] / b[k];
        assert (DivPrefix(a, b, i) + [a[i] / b[i]])[k] == a[i] / b[i];
      }
    }
  }

  // Conclude sequence equality by extensionality (same length + same elements)
  assert DivPrefix(a, b, i + 1) == DivPrefix(a, b, i) + [a[i] / b[i]];
}

method ElementWiseDivision(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  requires forall k :: 0 <= k < |b| ==> b[k] != 0
  ensures |result| == |a|
  ensures forall k :: 0 <= k < |result| ==> result[k] == a[k] / b[k]
  ensures result == DivPrefix(a, b, |a|)
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> b[k] != 0
    invariant result == DivPrefix(a, b, i)
  {
    // For-loop index is always within bounds in the body
    assert i < |a|;
    assert b[i] != 0;

    // Establish lemma precondition from the method precondition
    assert forall k :: 0 <= k < i + 1 ==> b[k] != 0 by
    {
      forall k | 0 <= k < i + 1 ensures b[k] != 0
      {
        // From loop bounds: i < |a| == |b|, so k < |b|
        assert k <= i;
        assert i < |a|;
        assert |a| == |b|;
        assert k < |b|;
      }
    };

    DivPrefixExtend(a, b, i);
    result := result + [a[i] / b[i]];
    assert result == DivPrefix(a, b, i + 1);
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
