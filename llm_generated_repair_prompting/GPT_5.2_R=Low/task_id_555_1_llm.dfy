// Returns the difference between the sum of the cubes and the
// sum of the first n positive natural numbers.

function {:fuel 20} CubeSum(n: nat): nat
{
  if n == 0 then 0 else CubeSum(n - 1) + n * n * n
}

function {:fuel 20} NumSum(n: nat): nat
{
  if n == 0 then 0 else NumSum(n - 1) + n
}

method DifferenceSumCubesAndSumNumbers(n: nat) returns (diff: int)
  ensures diff == CubeSum(n) as int - NumSum(n) as int
{
  var sumCubes := SumCubes(n);
  var sumNumbers := SumNumbers(n);
  return sumCubes as int - sumNumbers as int; //added 'as int' to convert nat to int
}

// Computes  the sum of the cubes of the first n positive natural numbers.
method SumCubes(n: nat) returns (s: nat)
  ensures s == CubeSum(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == CubeSum(i)
  {
    i := i + 1;
    s := s + i * i * i;
    assert s == CubeSum(i);
  }
}

// Computes the sum of the first n positive natural numbers.
method SumNumbers(n: nat) returns (s: nat)
  ensures s == NumSum(n)
{
  s := 0;
  var i : nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == NumSum(i)
  {
    i := i + 1;
    s := s + i;
    assert s == NumSum(i);
  }
}

// Test cases checked statically.
method DifferenceSumCubesAndSumNumbersTest(){
  var res4 := DifferenceSumCubesAndSumNumbers(0);
  assert res4 == 0;

  var res5 := DifferenceSumCubesAndSumNumbers(1);
  assert res5 == 0;

  var res6 := DifferenceSumCubesAndSumNumbers(2);
  assert res6 == 6; // (1+8) - (1+2)

  var res1:= DifferenceSumCubesAndSumNumbers(3);
  assert res1==30;
}
