// Returns the sum of the minimum and maximum elements of a non-empty array
function {:fuel 3} MinSeq(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then
    s[0]
  else
    (var m := MinSeq(s[..|s|-1]);
     if s[|s|-1] < m then s[|s|-1] else m)
}

function {:fuel 3} MaxSeq(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then
    s[0]
  else
    (var m := MaxSeq(s[..|s|-1]);
     if s[|s|-1] > m then s[|s|-1] else m)
}

method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == MinSeq(a[..]) + MaxSeq(a[..])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal == MinSeq(a[..i])
    invariant maxVal == MaxSeq(a[..i])
  {
    var prevMin := minVal;
    var prevMax := maxVal;

    if a[i] < minVal {
      minVal := a[i];
    } 
    if a[i] > maxVal {
      maxVal := a[i];
    }

    assert minVal == (if a[i] < prevMin then a[i] else prevMin);
    assert prevMin == MinSeq(a[..i]);
    assert minVal == MinSeq(a[..i+1]);

    assert maxVal == (if a[i] > prevMax then a[i] else prevMax);
    assert prevMax == MaxSeq(a[..i]);
    assert maxVal == MaxSeq(a[..i+1]);
  }
  sum := minVal + maxVal;
}





// Test cases checked statically.
method SumMinMaxTest(){
  var a1 := new int[] [1,2,3];
  var out1 := SumMinMax(a1);
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  var out3 := SumMinMax(a3);
  assert out3 == 8;
}

