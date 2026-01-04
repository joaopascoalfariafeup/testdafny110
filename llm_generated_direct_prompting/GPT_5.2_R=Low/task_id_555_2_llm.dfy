ghost function SumNumbersSpec(n: nat): nat
{
  if n == 0 then 0 else SumNumbersSpec(n - 1) + n
}

ghost function SumCubesSpec(n: nat): nat
{
  if n == 0 then 0 else SumCubesSpec(n - 1) + n * n * n
}

// Returns the difference between the sum of the cubes and the
// sum of the first n positive natural numbers.
method DifferenceSumCubesAndSumNumbers(n: nat) returns (diff: int)
  ensures diff == (SumCubesSpec(n) as int) - (SumNumbersSpec(n) as int)
{
  var sumCubes := SumCubes(n);
  var sumNumbers := SumNumbers(n);
  return sumCubes as int - sumNumbers as int; //added 'as int' to convert nat to int
}

// Computes  the sum of the cubes of the first n positive natural numbers.
method SumCubes(n: nat) returns (s: nat)
  ensures s == SumCubesSpec(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == SumCubesSpec(i as nat)
    decreases (n as int) - i
  {
    i := i + 1;
    s := s + i * i * i;
  }
}

// Computes the sum of the first n positive natural numbers.
method SumNumbers(n: nat) returns (s: nat)
  ensures s == SumNumbersSpec(n)
{
  s := 0;
  var i : nat := 0;
  while i < n
    invariant i <= n
    invariant s == SumNumbersSpec(i)
    decreases n - i
  {
    i := i + 1;
    s := s + i;
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
