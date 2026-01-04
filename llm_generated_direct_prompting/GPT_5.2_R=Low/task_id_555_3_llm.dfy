// Returns the difference between the sum of the cubes and the
// sum of the first n positive natural numbers.

function {:fuel 3} SumCubesSpec(n: nat): nat
{
  if n == 0 then 0 else SumCubesSpec(n - 1) + n * n * n
}

function {:fuel 3} SumNumbersSpec(n: nat): nat
{
  if n == 0 then 0 else SumNumbersSpec(n - 1) + n
}

lemma SumCubesSpecUnfold(n: nat)
  ensures n == 0 ==> SumCubesSpec(n) == 0
  ensures n > 0 ==> SumCubesSpec(n) == SumCubesSpec(n - 1) + n * n * n
{
}

lemma SumNumbersSpecUnfold(n: nat)
  ensures n == 0 ==> SumNumbersSpec(n) == 0
  ensures n > 0 ==> SumNumbersSpec(n) == SumNumbersSpec(n - 1) + n
{
}

method DifferenceSumCubesAndSumNumbers(n: nat) returns (diff: int)
  ensures diff == SumCubesSpec(n) as int - SumNumbersSpec(n) as int
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
    invariant s == SumCubesSpec(i)
  {
    i := i + 1;
    SumCubesSpecUnfold(i);
    assert SumCubesSpec(i) == SumCubesSpec(i - 1) + i * i * i;
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
    invariant 0 <= i <= n
    invariant s == SumNumbersSpec(i)
  {
    i := i + 1;
    SumNumbersSpecUnfold(i);
    assert SumNumbersSpec(i) == SumNumbersSpec(i - 1) + i;
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
