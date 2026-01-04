
// Computes the sum of the first 'n' elements of an array 'a'.
method CalcArraySum(a: array<int>,  n: nat := a.Length) returns (sum: int)
  requires n <= a.Length
  ensures sum == (if n == 0 then 0 else (sum a[..n]))
{
    sum := 0;
    for k := 0 to n
      invariant 0 <= k <= n
      invariant sum == (if k == 0 then 0 else (sum a[..k]))
    {
        sum := sum + a[k];
    }
    return sum;
}

// Test cases checked statically.
method ArraySumTest(){
  var a1 := new int[] [1, 2, 3];
  var s10 := CalcArraySum(a1, 1);
  assert s10 == 1;
  var s1 := CalcArraySum(a1);
  assert s1 == 6;

  var a2 := new int[] [15, 12, 13, 10];
  var s20 := CalcArraySum(a2, 1);
  assert s20 == 15;
  var s21 := CalcArraySum(a2, 2);
  assert s21 == 27;
  var s2 := CalcArraySum(a2);
  assert s2 == 50;

  var a3 := new int[] [];
  var s3 := CalcArraySum(a3);
  assert s3 == 0;
}

function sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
