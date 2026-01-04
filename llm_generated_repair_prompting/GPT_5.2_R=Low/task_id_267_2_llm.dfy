// Calculate the sum of the squares of the first n odd numbers.
// (Not a very good example, because the sum can be calculated directly by a formula,
// but serves of a proof of the formula.)
function ClosedFormOddSquares(n: nat): int
{
    let N := n as int in
      N * (2 * N - 1) * (2 * N + 1) / 3
}

lemma ClosedFormOddSquaresStep(k: nat)
  ensures ClosedFormOddSquares(k + 1) == ClosedFormOddSquares(k) + (2 * (k as int) + 1) * (2 * (k as int) + 1)
{
    var K := k as int;
    calc {
        ClosedFormOddSquares(k + 1);
        == { }
        (K + 1) * (2 * (K + 1) - 1) * (2 * (K + 1) + 1) / 3;
        == { }
        (K + 1) * (2 * K + 1) * (2 * K + 3) / 3;
        == { }
        ((K + 1) * (4 * K * K + 8 * K + 3)) / 3;
        == { }
        (4 * K * K * K + 12 * K * K + 11 * K + 3) / 3;
        == { }
        (4 * K * K * K + 12 * K * K - K) / 3 + (4 * K * K + 12 * K + 3) / 3;
        == { }
        K * (2 * K - 1) * (2 * K + 1) / 3 + (2 * K + 1) * (2 * K + 1);
        == { }
        ClosedFormOddSquares(k) + (2 * (k as int) + 1) * (2 * (k as int) + 1);
    }
}

method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (sum: int)
  ensures sum == ClosedFormOddSquares(n)
{
    sum := 0;
    var i := 1;
    for k: nat := 0 to n
      invariant 0 <= k <= n
      invariant i == 2 * (k as int) + 1
      invariant sum == ClosedFormOddSquares(k)
    {
        sum := sum + i * i;
        i := i + 2;
        ClosedFormOddSquaresStep(k);
        assert sum == ClosedFormOddSquares(k + 1);
        assert i == 2 * ((k + 1) as int) + 1;
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
