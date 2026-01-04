// Calculate the sum of the squares of the first n odd numbers.
// (Not a very good example, because the sum can be calculated directly by a formula,
// but serves of a proof of the formula.)
lemma OddSquaresClosedFormStep(k: int)
  requires k >= 0
  ensures k*(2*k-1)*(2*k+1) + 3*(2*k+1)*(2*k+1) == (k+1)*(2*(k+1)-1)*(2*(k+1)+1)
{
  calc {
    k*(2*k-1)*(2*k+1) + 3*(2*k+1)*(2*k+1);
    == { }
    k*((2*k-1)*(2*k+1)) + 3*((2*k+1)*(2*k+1));
    == { }
    k*(4*k*k - 1) + 3*(4*k*k + 4*k + 1);
    == { }
    (4*k*k*k - k) + (12*k*k + 12*k + 3);
    == { }
    4*k*k*k + 12*k*k + 11*k + 3;
    == { }
    (k+1)*(4*k*k + 8*k + 3);
    == { }
    (k+1)*((2*k+1)*(2*k+3));
    == { }
    (k+1)*(2*(k+1)-1)*(2*(k+1)+1);
  }
}

method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (sum: int)
  ensures sum >= 0
  ensures 3*sum == (n as int)*(2*(n as int)-1)*(2*(n as int)+1)
{
    sum := 0;
    var i := 1;
    for k := 0 to n
      invariant 0 <= k <= n
      invariant i == 2*k + 1
      invariant sum >= 0
      invariant 3*sum == k*(2*k-1)*(2*k+1)
    {
        sum := sum + i * i;
        assert i == 2*k + 1;
        assert 3*sum == k*(2*k-1)*(2*k+1) + 3*(2*k+1)*(2*k+1);
        OddSquaresClosedFormStep(k);
        assert 3*sum == (k+1)*(2*(k+1)-1)*(2*(k+1)+1);
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
