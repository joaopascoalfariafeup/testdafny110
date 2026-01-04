// Calculate the sum of the squares of the first n odd numbers.
// (Not a very good example, because the sum can be calculated directly by a formula,
// but serves of a proof of the formula.)

function Odd(m: nat): int {
  2 * m - 1
}

{:fuel 10}
function OddSquareSum(m: nat): int
  decreases m
{
  if m == 0 then 0 else OddSquareSum(m - 1) + Odd(m) * Odd(m)
}

lemma OddSucc(m: nat)
  ensures Odd(m + 1) == Odd(m) + 2
{
  calc {
    Odd(m + 1);
    2 * (m + 1) - 1;
    2 * m + 2 - 1;
    2 * m - 1 + 2;
    Odd(m) + 2;
  }
}

method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (sum: int)
  ensures sum == OddSquareSum(n)
{
    sum := 0;
    var i := 1;
    for k := 0 to n
      invariant sum == OddSquareSum(k)
      invariant i == Odd(k + 1)
    {
        sum := sum + i * i;
        assert sum == OddSquareSum(k) + Odd(k + 1) * Odd(k + 1);
        assert OddSquareSum(k + 1) == OddSquareSum(k) + Odd(k + 1) * Odd(k + 1);
        assert sum == OddSquareSum(k + 1);

        i := i + 2;
        OddSucc(k + 1);
        assert i == Odd(k + 2);
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
