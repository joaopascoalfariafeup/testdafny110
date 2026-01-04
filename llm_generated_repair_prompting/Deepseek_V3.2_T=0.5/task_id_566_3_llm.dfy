
// Computes the sum of the decimal digits of a natural number n.
method CalcSumOfDigits(n: nat) returns (sum: nat)
  ensures sum == SumOfDigitsSeq(NumberToSeq(n))
{
    sum := 0; // partial sum
    var num : nat := n; // remaining number
    while num > 0           
      invariant sum + SumOfDigitsSeq(NumberToSeq(num)) == SumOfDigitsSeq(NumberToSeq(n))
      invariant num >= 0
    {
        // Helper assertions to prove the invariant
        var old_sum := sum;
        var old_num := num;
        sum := sum + num % 10;
        num := num / 10;
        // Prove invariant preservation
        // Lemma: SumOfDigitsSeq(NumberToSeq(k)) == (k % 10) + SumOfDigitsSeq(NumberToSeq(k / 10)) for k > 0
        assert NumberToSeq(old_num) == [old_num % 10] + NumberToSeq(old_num / 10) by {
            if old_num > 0 {
                assert NumberToSeq(old_num) == [old_num % 10] + NumberToSeq(old_num / 10);
            }
        }
        assert SumOfDigitsSeq(NumberToSeq(old_num)) == (old_num % 10) + SumOfDigitsSeq(NumberToSeq(old_num / 10)) by {
            calc {
                SumOfDigitsSeq(NumberToSeq(old_num));
                == // by definition of NumberToSeq when old_num > 0
                SumOfDigitsSeq([old_num % 10] + NumberToSeq(old_num / 10));
                == // by definition of SumOfDigitsSeq
                (old_num % 10) + SumOfDigitsSeq(NumberToSeq(old_num / 10));
            }
        }
        assert old_sum + SumOfDigitsSeq(NumberToSeq(old_num)) == old_sum + (old_num % 10) + SumOfDigitsSeq(NumberToSeq(old_num / 10));
        assert old_sum + (old_num % 10) + SumOfDigitsSeq(NumberToSeq(old_num / 10)) == sum + SumOfDigitsSeq(NumberToSeq(num));
    }
    // When loop ends, num == 0
    if num == 0 {
        assert SumOfDigitsSeq(NumberToSeq(num)) == 0;
        assert sum == SumOfDigitsSeq(NumberToSeq(n));
    }
}

ghost function SumOfDigitsSeq(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 0 else s[|s|-1] + SumOfDigitsSeq(s[..|s|-1])
}

ghost function NumberToSeq(n: nat): seq<nat>
  decreases n
{
  if n == 0 then [] else [n % 10] + NumberToSeq(n / 10)
}

// Test cases checked statically by Dafny.
method SumOfDigitsTest() {
    var s1 := CalcSumOfDigits(0);
    assert s1 == 0;
    var s2 := CalcSumOfDigits(9);
    assert s2 == 9;
    var s3 := CalcSumOfDigits(10);
    assert s3 == 1;
    var s4 := CalcSumOfDigits(99);
    assert s4 == 18;
    var s5 := CalcSumOfDigits(111111111);
    // Helper assertion for the specific case
    assert NumberToSeq(111111111) == [1,1,1,1,1,1,1,1,1] by {
        calc {
            NumberToSeq(111111111);
            == [111111111 % 10] + NumberToSeq(111111111 / 10);
            == [1] + NumberToSeq(11111111);
            == [1] + ([11111111 % 10] + NumberToSeq(11111111 / 10));
            == [1] + ([1] + NumberToSeq(1111111));
            == [1,1] + NumberToSeq(1111111);
            == [1,1] + ([1111111 % 10] + NumberToSeq(1111111 / 10));
            == [1,1] + ([1] + NumberToSeq(111111));
            == [1,1,1] + NumberToSeq(111111);
            == [1,1,1] + ([111111 % 10] + NumberToSeq(111111 / 10));
            == [1,1,1] + ([1] + NumberToSeq(11111));
            == [1,1,1,1] + NumberToSeq(11111);
            == [1,1,1,1] + ([11111 % 10] + NumberToSeq(11111 / 10));
            == [1,1,1,1] + ([1] + NumberToSeq(1111));
            == [1,1,1,1,1] + NumberToSeq(1111);
            == [1,1,1,1,1] + ([1111 % 10] + NumberToSeq(1111 / 10));
            == [1,1,1,1,1] + ([1] + NumberToSeq(111));
            == [1,1,1,1,1,1] + NumberToSeq(111);
            == [1,1,1,1,1,1] + ([111 % 10] + NumberToSeq(111 / 10));
            == [1,1,1,1,1,1] + ([1] + NumberToSeq(11));
            == [1,1,1,1,1,1,1] + NumberToSeq(11);
            == [1,1,1,1,1,1,1] + ([11 % 10] + NumberToSeq(11 / 10));
            == [1,1,1,1,1,1,1] + ([1] + NumberToSeq(1));
            == [1,1,1,1,1,1,1,1] + NumberToSeq(1);
            == [1,1,1,1,1,1,1,1] + ([1 % 10] + NumberToSeq(1 / 10));
            == [1,1,1,1,1,1,1,1] + ([1] + NumberToSeq(0));
            == [1,1,1,1,1,1,1,1,1] + [];
            == [1,1,1,1,1,1,1,1,1];
        }
    }
    assert SumOfDigitsSeq([1,1,1,1,1,1,1,1,1]) == 9 by {
        calc {
            SumOfDigitsSeq([1,1,1,1,1,1,1,1,1]);
            == 1 + SumOfDigitsSeq([1,1,1,1,1,1,1,1]);
            == 1 + (1 + SumOfDigitsSeq([1,1,1,1,1,1,1]));
            == 1 + 1 + (1 + SumOfDigitsSeq([1,1,1,1,1,1]));
            == 1 + 1 + 1 + (1 + SumOfDigitsSeq([1,1,1,1,1]));
            == 1 + 1 + 1 + 1 + (1 + SumOfDigitsSeq([1,1,1,1]));
            == 1 + 1 + 1 + 1 + 1 + (1 + SumOfDigitsSeq([1,1,1]));
            == 1 + 1 + 1 + 1 + 1 + 1 + (1 + SumOfDigitsSeq([1,1]));
            == 1 + 1 + 1 + 1 + 1 + 1 + 1 + (1 + SumOfDigitsSeq([1]));
            == 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (1 + SumOfDigitsSeq([]));
            == 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 0;
            == 9;
        }
    }
    assert s5 == 9;
}


