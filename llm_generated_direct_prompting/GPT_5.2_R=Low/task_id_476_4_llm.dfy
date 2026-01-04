// Returns the sum of the minimum and maximum elements of a non-empty array
function MinUpTo(s: seq<int>, n: int): int
  requires 1 <= n <= |s|
  decreases n
{
  if n == 1 then s[0]
  else
    var m := MinUpTo(s, n - 1);
    if s[n - 1] < m then s[n - 1] else m
}

function MaxUpTo(s: seq<int>, n: int): int
  requires 1 <= n <= |s|
  decreases n
{
  if n == 1 then s[0]
  else
    var m := MaxUpTo(s, n - 1);
    if s[n - 1] > m then s[n - 1] else m
}

method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == MinUpTo(a[..], a.Length) + MaxUpTo(a[..], a.Length)
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal == MinUpTo(a[..], i)
    invariant maxVal == MaxUpTo(a[..], i)
  {
    if a[i] < minVal {
      minVal := a[i];
    } 
    if a[i] > maxVal {
      maxVal := a[i];
    }
    assert minVal == MinUpTo(a[..], i + 1);
    assert maxVal == MaxUpTo(a[..], i + 1);
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

