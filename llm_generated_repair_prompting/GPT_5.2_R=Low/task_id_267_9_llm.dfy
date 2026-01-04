// Calculate the sum of the squares of the first n odd numbers.
// (Not a very good example, because the sum can be calculated directly by a formula,
// but serves of a proof of the formula.)
function ClosedFormOddSquares(n: nat): int
{
  (n as int) * (2 * (n as int) - 1) * (2 * (n as int) + 1) / 3
}

// Helpful arithmetic fact about Euclidean integer division by 3
lemma DivPlusMultipleOf3(a: int, s: int)
  ensures (a + 3*s) / 3 == a / 3 + s
{
  // Z3 can prove this directly from the axioms of Euclidean division
}

// A robust polynomial identity used by ClosedFormOddSquaresStep (no division involved)
lemma PolyIdentityOddSquares(K: int)
  ensures (K + 1) * (2 * K + 1) * (2 * K + 3)
       == K * (2 * K - 1) * (2 * K + 1) + 3 * ((2 * K + 1) * (2 * K + 1))
{
  calc {
    (K + 1) * (2 * K + 1) * (2 * K + 3);
    == { }
    (K + 1) * ((2 * K + 1) * (2 * K + 3));
    == { }
    (K + 1) * (4 * K * K + 8 * K + 3);
    == { }
    K * (4 * K * K + 8 * K + 3) + (4 * K * K + 8 * K + 3);
    == { }
    (4 * K * K * K + 8 * K * K + 3 * K) + (4 * K * K + 8 * K + 3);
    == { }
    4 * K * K * K + 12 * K * K + 11 * K + 3;
    == { }
    (4 * K * K * K - K) + (12 * K * K + 12 * K + 3);
    == { }
    K * (4 * K * K - 1) + 3 * (4 * K * K + 4 * K + 1);
    == { }
    K * ((2 * K - 1) * (2 * K + 1)) + 3 * ((2 * K + 1) * (2 * K + 1));
    == { }
    K * (2 * K - 1) * (2 * K + 1) + 3 * ((2 * K + 1) * (2 * K + 1));
  }
}

lemma ClosedFormOddSquaresStep(k: nat)
  ensures ClosedFormOddSquares(k + 1) == ClosedFormOddSquares(k) + (2 * (k as int) + 1) * (2 * (k as int) + 1)
{
  var K := k as int;
  var s := (2 * K + 1) * (2 * K + 1);

  // First prove the key polynomial identity (no division involved)
  PolyIdentityOddSquares(K);
  assert (K + 1) * (2 * K + 1) * (2 * K + 3)
       == K * (2 * K - 1) * (2 * K + 1) + 3 * s;

  // Now do the division step using DivPlusMultipleOf3 (avoids splitting /3 over +)
  calc {
    ClosedFormOddSquares(k + 1);
    == { }
    (K + 1) * (2 * K + 1) * (2 * K + 3) / 3;
    == { }
    (K * (2 * K - 1) * (2 * K + 1) + 3 * s) / 3;
    == { DivPlusMultipleOf3(K * (2 * K - 1) * (2 * K + 1), s); }
    (K * (2 * K - 1) * (2 * K + 1)) / 3 + s;
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
