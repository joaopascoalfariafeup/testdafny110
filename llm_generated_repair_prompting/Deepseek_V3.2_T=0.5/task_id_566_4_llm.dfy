
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
            // This follows from the definition of NumberToSeq when old_num > 0
            // We need to help Dafny see this
            if old_num > 0 {
                // The recursive definition directly gives us this
                // NumberToSeq(old_num) = [old_num % 10] + NumberToSeq(old_num / 10)
                // This is exactly the recursive case of NumberToSeq
            }
        }
        assert SumOfDigitsSeq(NumberToSeq(old_num)) == (old_num % 10) + SumOfDigitsSeq(NumberToSeq(old_num / 10)) by {
            // Use the property of SumOfDigitsSeq on concatenated sequences
            calc {
                SumOfDigitsSeq(NumberToSeq(old_num));
                == // by the property we just proved about NumberToSeq
                SumOfDigitsSeq([old_num % 10] + NumberToSeq(old_num / 10));
                == // by definition of SumOfDigitsSeq on non-empty sequence
                (old_num % 10) + SumOfDigitsSeq(NumberToSeq(old_num / 10));
            }
        }
        // Now the invariant preservation follows
        calc {
            old_sum + SumOfDigitsSeq(NumberToSeq(old_num));
            == old_sum + ((old_num % 10) + SumOfDigitsSeq(NumberToSeq(old_num / 10)));
            == (old_sum + (old_num % 10)) + SumOfDigitsSeq(NumberToSeq(old_num / 10));
            == sum + SumOfDigitsSeq(NumberToSeq(num));
        }
    }
    // When loop ends, num == 0
    if num == 0 {
        assert SumOfDigitsSeq(NumberToSeq(num)) == 0;
        assert sum == SumOfDigitsSeq(NumberToSeq(n));
    }
}

ghost function SumOfDigitsSeq(s: seq<nat>): nat
  decreases |s|
  ensures |s| == 0 ==> SumOfDigitsSeq(s) == 0
  ensures |s| > 0 ==> SumOfDigitsSeq(s) == s[|s|-1] + SumOfDigitsSeq(s[..|s|-1])
{
  if |s| == 0 then 0 else s[|s|-1] + SumOfDigitsSeq(s[..|s|-1])
}

ghost function NumberToSeq(n: nat): seq<nat>
  decreases n
  ensures n == 0 ==> NumberToSeq(n) == []
  ensures n > 0 ==> NumberToSeq(n) == [n % 10] + NumberToSeq(n / 10)
{
  if n == 0 then [] else [n % 10] + NumberToSeq(n / 10)
}

// Helper lemma to prove properties about SumOfDigitsSeq
lemma SumOfDigitsSeqConcat(a: seq<nat>, b: seq<nat>)
  ensures SumOfDigitsSeq(a + b) == SumOfDigitsSeq(a) + SumOfDigitsSeq(b)
  decreases |a|
{
  if |a| == 0 {
    // Base case: empty sequence
    assert a + b == b;
  } else {
    // Recursive case
    calc {
      SumOfDigitsSeq(a + b);
      == (a + b)[|a + b|-1] + SumOfDigitsSeq((a + b)[..|a + b|-1]);
      == b[|b|-1] + SumOfDigitsSeq(a + b[..|b|-1]);
      == b[|b|-1] + (SumOfDigitsSeq(a) + SumOfDigitsSeq(b[..|b|-1]));
      == SumOfDigitsSeq(a) + (b[|b|-1] + SumOfDigitsSeq(b[..|b|-1]));
      == SumOfDigitsSeq(a) + SumOfDigitsSeq(b);
    }
  }
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
    // Instead of a long calculation, we can use a simpler approach
    // First, let's compute NumberToSeq(111111111) step by step
    var seq1 := NumberToSeq(111111111);
    // We know it should be [1,1,1,1,1,1,1,1,1]
    // Let's verify this by checking its length and elements
    assert |seq1| == 9 by {
        // Each division by 10 reduces the number until 0
        // 111111111 has 9 digits
    }
    // Now compute SumOfDigitsSeq of this sequence
    var sum1 := SumOfDigitsSeq(seq1);
    // Since all elements are 1, the sum is 9
    assert sum1 == 9 by {
        // Use the postcondition of SumOfDigitsSeq
        if |seq1| == 0 {
            // Not the case
        } else {
            // Recursively compute
            var tail := seq1[..|seq1|-1];
            calc {
                sum1;
                == seq1[|seq1|-1] + SumOfDigitsSeq(tail);
                == 1 + SumOfDigitsSeq(tail);
                // Continue recursively
            }
        }
    }
    assert s5 == 9;
}

