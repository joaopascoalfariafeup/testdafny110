
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
    assert SumOfDigitsSeq(a) == 0;
  } else {
    // Recursive case: a is non-empty
    var a_last := a[|a|-1];
    var a_prefix := a[..|a|-1];
    // Use induction on a
    SumOfDigitsSeqConcat(a_prefix, [a_last] + b);
    calc {
      SumOfDigitsSeq(a + b);
      == SumOfDigitsSeq(a_prefix + [a_last] + b);
      == SumOfDigitsSeq(a_prefix) + SumOfDigitsSeq([a_last] + b);
      == SumOfDigitsSeq(a_prefix) + (a_last + SumOfDigitsSeq(b));
      == (SumOfDigitsSeq(a_prefix) + a_last) + SumOfDigitsSeq(b);
      == SumOfDigitsSeq(a) + SumOfDigitsSeq(b);
    }
  }
}

// Simpler lemma: SumOfDigitsSeq of a single element plus a sequence
lemma SumOfDigitsSeqSinglePlusSeq(x: nat, s: seq<nat>)
  ensures SumOfDigitsSeq([x] + s) == x + SumOfDigitsSeq(s)
{
  // Direct from definition
  calc {
    SumOfDigitsSeq([x] + s);
    == ([x] + s)[|([x] + s)|-1] + SumOfDigitsSeq(([x] + s)[..|([x] + s)|-1]);
    == {
      if |s| == 0 {
        assert ([x] + s) == [x];
        x + SumOfDigitsSeq([]);
      } else {
        s[|s|-1] + SumOfDigitsSeq([x] + s[..|s|-1]);
      }
    }
    == x + SumOfDigitsSeq(s);
  }
}

// Better: prove the needed property directly for the loop
lemma SumOfDigitsSeqNumberToSeqProperty(k: nat)
  requires k > 0
  ensures SumOfDigitsSeq(NumberToSeq(k)) == (k % 10) + SumOfDigitsSeq(NumberToSeq(k / 10))
{
  // Direct from definitions
  calc {
    SumOfDigitsSeq(NumberToSeq(k));
    == SumOfDigitsSeq([k % 10] + NumberToSeq(k / 10));  // by definition of NumberToSeq when k > 0
    == (k % 10) + SumOfDigitsSeq(NumberToSeq(k / 10));  // by lemma SumOfDigitsSeqSinglePlusSeq
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
    // Now compute SumOfDigitsSeq of this sequence
    var sum1 := SumOfDigitsSeq(seq1);
    // Since all elements are 1, the sum is 9
    // Use a simple calculation with fuel
    // Simpler: just assert the final result based on the method's postcondition
    // The method ensures s5 == SumOfDigitsSeq(NumberToSeq(111111111))
    // We can compute NumberToSeq(111111111) manually in Dafny
    var n := 111111111;
    var seq2 := NumberToSeq(n);
    // Add fuel to help Dafny compute
    // Actually, we can just trust the method's implementation
    // The test will verify if the assertion holds
    assert s5 == 9 by {
        // Use the property that sum of digits of 111111111 is 9
        // This is a simple arithmetic fact
        // We can prove it by noting that 111111111 has 9 digits, all 1's
        // So SumOfDigitsSeq(NumberToSeq(111111111)) = 9 * 1 = 9
        // Let's compute it step by step
        calc {
            s5;
            == SumOfDigitsSeq(NumberToSeq(111111111));
            == SumOfDigitsSeq([1,1,1,1,1,1,1,1,1]);
            == 1 + SumOfDigitsSeq([1,1,1,1,1,1,1,1]);
            == 1 + 1 + SumOfDigitsSeq([1,1,1,1,1,1,1]);
            == 1 + 1 + 1 + SumOfDigitsSeq([1,1,1,1,1,1]);
            == 1 + 1 + 1 + 1 + SumOfDigitsSeq([1,1,1,1,1]);
            == 1 + 1 + 1 + 1 + 1 + SumOfDigitsSeq([1,1,1,1]);
            == 1 + 1 + 1 + 1 + 1 + 1 + SumOfDigitsSeq([1,1,1]);
            == 1 + 1 + 1 + 1 + 1 + 1 + 1 + SumOfDigitsSeq([1,1]);
            == 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + SumOfDigitsSeq([1]);
            == 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + SumOfDigitsSeq([]);
            == 9;
        }
    }
}




