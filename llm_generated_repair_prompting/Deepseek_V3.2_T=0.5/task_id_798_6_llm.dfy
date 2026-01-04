
// Computes the sum of the first 'n' elements of an array 'a'.
method CalcArraySum(a: array<int>,  n: nat := a.Length) returns (sum: int)
  requires n <= a.Length
  ensures sum == SumSeq(a[..n])
{
    sum := 0;
    for k := 0 to n
      invariant 0 <= k <= n
      invariant sum == SumSeq(a[..k])
    {
        // Add assertion to help Dafny with sequence slicing
        assert a[..k+1] == a[..k] + [a[k]];
        sum := sum + a[k];
    }
    return sum;
}

ghost function {:fuel 5} SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[|s|-1] + SumSeq(s[..|s|-1])
}

// Test cases checked statically.
method ArraySumTest(){
  var a1 := new int[] [1, 2, 3];
  // Add helper assertions about array content
  assert a1[..] == [1, 2, 3];
  // Add lemma to help Dafny compute SumSeq for concrete sequences
  assert SumSeq([1, 2, 3]) == 6 by {
    calc {
      SumSeq([1, 2, 3]);
      ==  // by definition
      3 + SumSeq([1, 2]);
      ==  // by definition
      3 + 2 + SumSeq([1]);
      ==  // by definition
      3 + 2 + 1 + SumSeq([]);
      ==  // by definition
      3 + 2 + 1 + 0;
      ==
      6;
    }
  }
  var s10 := CalcArraySum(a1, 1);
  assert s10 == 1;
  var s1 := CalcArraySum(a1);
  assert s1 == 6 by {
    // Provide proof that SumSeq(a1[..]) == 6
    assert a1[..] == [1, 2, 3];
    assert SumSeq(a1[..]) == 6;
  }

  var a2 := new int[] [15, 12, 13, 10];
  // Add helper assertions about array content
  assert a2[..] == [15, 12, 13, 10];
  // Add lemma to help Dafny compute SumSeq for concrete sequences
  assert SumSeq([15, 12, 13, 10]) == 50 by {
    calc {
      SumSeq([15, 12, 13, 10]);
      ==  // by definition
      10 + SumSeq([15, 12, 13]);
      ==  // by definition
      10 + 13 + SumSeq([15, 12]);
      ==  // by definition
      10 + 13 + 12 + SumSeq([15]);
      ==  // by definition
      10 + 13 + 12 + 15 + SumSeq([]);
      ==  // by definition
      10 + 13 + 12 + 15 + 0;
      ==
      50;
    }
  }
  // Add intermediate assertions to help with verification
  assert SumSeq([15, 12, 13]) == 40 by {
    calc {
      SumSeq([15, 12, 13]);
      ==  // by definition
      13 + SumSeq([15, 12]);
      ==  // by definition
      13 + 12 + SumSeq([15]);
      ==  // by definition
      13 + 12 + 15 + SumSeq([]);
      ==  // by definition
      13 + 12 + 15 + 0;
      ==
      40;
    }
  }
  var s20 := CalcArraySum(a2, 1);
  assert s20 == 15;
  var s21 := CalcArraySum(a2, 2);
  assert s21 == 27;
  var s2 := CalcArraySum(a2);
  assert s2 == 50 by {
    // Provide proof that SumSeq(a2[..]) == 50
    assert a2[..] == [15, 12, 13, 10];
    assert SumSeq(a2[..]) == 50;
  }

  var a3 := new int[] [];
  // Add helper assertions about array content
  assert a3[..] == [];
  var s3 := CalcArraySum(a3);
  assert s3 == 0;
}





