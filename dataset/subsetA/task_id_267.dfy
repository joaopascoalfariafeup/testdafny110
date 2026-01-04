// Calculate the sum of the squares of the first n odd numbers.
// (Not a very good example, because the sum can be calculated directly by a formula,
// but serves of a proof of the formula.)
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (sum: int)
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    sum := 0;
    var i := 1;
    for k := 0 to n
        invariant sum == k * (2 * k - 1) * (2 * k + 1) / 3
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
  assert out2 == 10;

  var out3:=SumOfSquaresOfFirstNOddNumbers(3);
  assert out3 == 35;
}