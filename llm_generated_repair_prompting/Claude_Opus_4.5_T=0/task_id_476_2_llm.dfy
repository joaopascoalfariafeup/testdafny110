// Ghost function to compute minimum of a sequence
ghost function {:fuel 5} seqMin(s: seq<int>): int
  requires |s| > 0
  ensures seqMin(s) in s
  ensures forall k :: 0 <= k < |s| ==> seqMin(s) <= s[k]
{
  if |s| == 1 then s[0]
  else if s[|s|-1] < seqMin(s[..|s|-1]) then s[|s|-1]
  else seqMin(s[..|s|-1])
}

// Ghost function to compute maximum of a sequence
ghost function {:fuel 5} seqMax(s: seq<int>): int
  requires |s| > 0
  ensures seqMax(s) in s
  ensures forall k :: 0 <= k < |s| ==> seqMax(s) >= s[k]
{
  if |s| == 1 then s[0]
  else if s[|s|-1] > seqMax(s[..|s|-1]) then s[|s|-1]
  else seqMax(s[..|s|-1])
}

// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == seqMin(a[..]) + seqMax(a[..])
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && sum == a[i] + a[j] && (forall k :: 0 <= k < a.Length ==> a[i] <= a[k]) && (forall k :: 0 <= k < a.Length ==> a[j] >= a[k])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant exists idx :: 0 <= idx < a.Length && minVal == a[idx]
    invariant exists idx :: 0 <= idx < a.Length && maxVal == a[idx]
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k :: 0 <= k < i ==> maxVal >= a[k]
    invariant minVal == seqMin(a[..i])
    invariant maxVal == seqMax(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] < minVal {
      minVal := a[i];
    } 
    if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  assert a[..a.Length] == a[..];
  sum := minVal + maxVal;
}





// Test cases checked statically.
method SumMinMaxTest(){
  var a1 := new int[] [1,2,3];
  assert a1[..] == [1,2,3];
  var out1 := SumMinMax(a1);
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  assert a2[..] == [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  assert a3[..] == [2,3,6];
  var out3 := SumMinMax(a3);
  assert out3 == 8;
}
