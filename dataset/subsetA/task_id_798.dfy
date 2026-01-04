// Recursive definition of the sum of the elements of an array 'a',
// from index 'i' (inclusive) to index 'j' (exclusive).
// The 'fuel' attribute helps checking the assertions in the test cases.
ghost function ArraySum(a: array<int>, i: nat := 0, j: nat := a.Length) : int
  requires 0 <= i <= j <= a.Length
  reads a
{
  if j <= i then 0 else ArraySum(a, i, j-1) + a[j-1]
}

// Computes the sum of the first 'n' elements of an array 'a'.
method CalcArraySum(a: array<int>,  n: nat := a.Length) returns (sum: int)
  requires 0 <= n <= a.Length
  ensures sum == ArraySum(a, 0, n)
{
    sum := 0;
    for k := 0 to n
        invariant sum == ArraySum(a, 0, k)
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