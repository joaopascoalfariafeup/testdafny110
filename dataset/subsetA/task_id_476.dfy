// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == Max(a[..]) + Min(a[..])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant maxVal == Max(a[..i])
    invariant minVal == Min(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]]; // proof helper
    if a[i] < minVal {
      minVal := a[i];
    } 
    if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  sum := minVal + maxVal;
  assert a[..a.Length] == a[..]; // proof helper
}

// Auxiliary function that gives the minimum element of a non-empty sequence.
ghost function {:fuel 4} Min(a: seq<int>) : int
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else if Last(a) <= Min(DropLast(a)) then Last(a) else Min(DropLast(a))
}

// Auxiliary function that gives the maximum element of a non-empty sequence.
ghost function {:fuel 4} Max(a: seq<int>) : int
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else if Last(a) >= Max(DropLast(a)) then Last(a) else Max(DropLast(a))
}

// Auxiliary function that gives the last element of a non-empty sequence
ghost function Last<T>(a: seq<T>): T
  requires |a| > 0
{
  a[|a| - 1]
}

// Auxiliary function that gives a sequence without the last element.
ghost function DropLast<T>(a: seq<T>): seq<T>
  requires |a| > 0
{
  a[0..|a| - 1]
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
