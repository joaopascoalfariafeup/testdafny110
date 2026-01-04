
// Helper function to calculate the sum of the squares of the first k odd numbers
ghost function {:fuel 5} SumSquaresUpTo(k: nat): int
{
  if k == 0 then 0 else SumSquaresUpTo(k-1) + (2*k-1)*(2*k-1)
}

// Calculate the sum of the squares of the first n odd numbers.
// (Not a very good example, because the sum can be calculated directly by a formula,
// but serves of a proof of the formula.)
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (sum: int)
    ensures sum == n * n * n
{
    sum := 0;
    var i := 1;
    for k := 0 to n
        invariant k <= n
        invariant sum == SumSquaresUpTo(k)
        invariant i == 2 * k + 1
    {
        sum := sum + i * i;
        i := i + 2;
    }
}

// Test cases checked statically.
method SumOfSquaresOfFirstNOddNumbersTest(){
  var out1 := SumOfSquaresOfFirstNOddNumbers(1);
  assert out1 == 1;

  var out2 := SumOfSquaresOfFirstNOddNumbers(2);
  assert out2 == 8;

  var out3:=SumOfSquaresOfFirstNOddNumbers(3);
  assert out3 == 27;
}

