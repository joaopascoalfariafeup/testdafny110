// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == Min(a) + Max(a)
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k :: 0 <= k < i ==> maxVal >= a[k]
  {
    if a[i] < minVal {
      minVal := a[i];
    } 
    if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  sum := minVal + maxVal;
}

function Min(a: array<int>): int
  requires a.Length > 0
{
  min(a[0], a[1..])
}

function min(x: int, a: array<int>): int
{
  if a.Length == 0 then x else min(if x < a[0] then x else a[0], a[1..])
}

function Max(a: array<int>): int
  requires a.Length > 0
{
  max(a[0], a[1..])
}

function max(x: int, a: array<int>): int
{
  if a.Length == 0 then x else max(if x > a[0] then x else a[0], a[1..])
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

