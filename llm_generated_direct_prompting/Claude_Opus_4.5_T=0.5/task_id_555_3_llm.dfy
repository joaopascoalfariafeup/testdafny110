// Returns the difference between the sum of the cubes and the
// sum of the first n positive natural numbers.

ghost function SumCubesFunc(n: nat): nat
{
  if n == 0 then 0 else n * n * n + SumCubesFunc(n - 1)
}

ghost function SumNumbersFunc(n: nat): nat
{
  if n == 0 then 0 else n + SumNumbersFunc(n - 1)
}

method DifferenceSumCubesAndSumNumbers(n: nat) returns (diff: int)
  ensures diff == SumCubesFunc(n) as int - SumNumbersFunc(n) as int
{
  var sumCubes := SumCubes(n);
  var sumNumbers := SumNumbers(n);
  return sumCubes as int - sumNumbers as int; //added 'as int' to convert nat to int
}

// Computes  the sum of the cubes of the first n positive natural numbers.
method SumCubes(n: nat) returns (s: nat)
  ensures s == SumCubesFunc(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == SumCubesFunc(i)
  {
    i := i + 1;
    s := s + i * i * i;
  }
}

// Computes the sum of the first n positive natural numbers.
method SumNumbers(n: nat) returns (s: nat)
  ensures s == SumNumbersFunc(n)
{
  s := 0;
  var i : nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == SumNumbersFunc(i)
  {
    i := i + 1;
    s := s + i;
  }
}

// Test cases checked statically.
method {:fuel SumCubesFunc, 4} {:fuel SumNumbersFunc, 4} DifferenceSumCubesAndSumNumbersTest(){
  var res4 := DifferenceSumCubesAndSumNumbers(0);
  assert res4 == 0;

  var res5 := DifferenceSumCubesAndSumNumbers(1);
  assert res5 == 0;

  var res6 := DifferenceSumCubesAndSumNumbers(2);
  assert res6 == 6; // (1+8) - (1+2)

  var res1:= DifferenceSumCubesAndSumNumbers(3);
  assert res1==30;
}
