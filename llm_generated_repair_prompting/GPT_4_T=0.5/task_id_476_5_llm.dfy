// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == Min(a, 0, a.Length-1) + Max(a, 0, a.Length-1)
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 0 <= i <= a.Length
    invariant minVal <= Min(a, 0, i-1) && maxVal >= Max(a, 0, i-1)
    invariant forall j :: 0 <= j < i ==> minVal <= a[j] && maxVal >= a[j]
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

// Auxiliary function to get the minimum value in a segment of an array
function {:fuel 5} Min(a: array<int>, start: int, end: int): int
  requires 0 <= start <= end < a.Length
  reads a
  decreases end - start
{
  if start == end then a[start] else if a[start] < Min(a, start + 1, end) then a[start] else Min(a, start + 1, end)
}

// Auxiliary function to get the maximum value in a segment of an array
function {:fuel 5} Max(a: array<int>, start: int, end: int): int
  requires 0 <= start <= end < a.Length
  reads a
  decreases end - start
{
  if start == end then a[start] else if a[start] > Max(a, start + 1, end) then a[start] else Max(a, start + 1, end)
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


