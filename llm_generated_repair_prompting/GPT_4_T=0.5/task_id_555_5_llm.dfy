// Returns the difference between the sum of the squares and the cube of the sum of the first n positive natural numbers.
method DifferenceSumCubesAndSumNumbers(n: nat) returns (diff: int)
  ensures diff == ((n*(n+1)/2)*(n*(n+1)/2) as int) - ((n*(n+1)*(2*n+1)/6) as int)
{
  var sumNumbers := SumNumbers(n);
  var sumCubes := SumCubes(n);
  diff := (sumNumbers*sumNumbers as int) - (sumCubes as int); //added 'as int' to convert nat to int
}

// Computes  the sum of the cubes of the first n positive natural numbers.
method SumCubes(n: nat) returns (s: nat)
  ensures s == n*(n+1)*(2*n+1)/6
{
  s := 0;
  var i := 0;
  while i < n
    invariant i <= n
    invariant s == ((i-1)*i*(2*i-1))/6
  {
    i := i + 1;
    s := s + i * i * i;
  }
}

// Computes the sum of the first n positive natural numbers.
method SumNumbers(n: nat) returns (s: nat)
  ensures s == n*(n+1)/2
{
  s := 0;
  var i : nat := 0;
  while i < n
    invariant i <= n
    invariant s == i*(i+1)/2
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
  assert res6 == 4; // (1+2)^2 - (1+8)

  var res1:= DifferenceSumCubesAndSumNumbers(3);
  assert res1==36; // (1+2+3)^2 - (1+8+27)
}

