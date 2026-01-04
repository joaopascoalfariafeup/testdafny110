// Auxiliary specification functions

function MinNat(a: nat, b: nat): nat {
  if a <= b then a else b
}

function {:fuel 50} CommonDivsUpTo(a: nat, b: nat, n: nat): seq<nat> {
  if n == 0 then
    []
  else
    if a % n == 0 && b % n == 0 then CommonDivsUpTo(a, b, n - 1) + [n]
    else CommonDivsUpTo(a, b, n - 1)
}

function {:fuel 50} commonDivisors(a: nat, b: nat): seq<nat> {
  CommonDivsUpTo(a, b, MinNat(a, b))
}

function {:fuel 50} SumSeq(s: seq<nat>): nat {
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

lemma SumSeqAppendOne(s: seq<nat>, x: nat)
  ensures SumSeq(s + [x]) == SumSeq(s) + x
  decreases |s|
{
  if |s| == 0 {
    // SumSeq([] + [x]) == SumSeq([x]) == 0 + x
  } else {
    // Induction on the prefix
    SumSeqAppendOne(s[..|s|-1], x);
    // Now unfold SumSeq on both sides:
    // SumSeq((s[..|s|-1] + [s[|s|-1]]) + [x]) = SumSeq(s[..|s|-1] + [s[|s|-1], x])
    // and SumSeq(s + [x]) = SumSeq(s[..|s|-1] + [s[|s|-1], x])
    assert s == s[..|s|-1] + [s[|s|-1]];
    assert s + [x] == (s[..|s|-1] + [s[|s|-1]]) + [x];
    assert (s[..|s|-1] + [s[|s|-1]]) + [x] == s[..|s|-1] + [s[|s|-1], x];
    // Unfold SumSeq at length >= 1
    assert SumSeq(s[..|s|-1] + [s[|s|-1], x]) ==
           SumSeq((s[..|s|-1] + [s[|s|-1], x])[..|(s[..|s|-1] + [s[|s|-1], x])|-1]) + x;
    assert (s[..|s|-1] + [s[|s|-1], x])[..|(s[..|s|-1] + [s[|s|-1], x])|-1] == s[..|s|-1] + [s[|s|-1]];
    assert SumSeq(s[..|s|-1] + [s[|s|-1], x]) == SumSeq(s[..|s|-1] + [s[|s|-1]]) + x;
    assert SumSeq(s[..|s|-1] + [s[|s|-1]]) == SumSeq(s[..|s|-1]) + s[|s|-1];
  }
}

// Small concrete evaluation helpers to keep the SMT solver fast in tests

lemma CommonDivisors_10_15()
  ensures commonDivisors(10, 15) == [1, 5]
{
  // MinNat(10,15)=10, so commonDivisors(10,15)=CommonDivsUpTo(10,15,10)
  assert MinNat(10, 15) == 10;
  assert commonDivisors(10, 15) == CommonDivsUpTo(10, 15, 10);

  assert CommonDivsUpTo(10, 15, 0) == [];
  assert CommonDivsUpTo(10, 15, 1) == CommonDivsUpTo(10, 15, 0) + [1];
  assert CommonDivsUpTo(10, 15, 1) == [1];

  assert CommonDivsUpTo(10, 15, 2) == CommonDivsUpTo(10, 15, 1);
  assert CommonDivsUpTo(10, 15, 3) == CommonDivsUpTo(10, 15, 2);
  assert CommonDivsUpTo(10, 15, 4) == CommonDivsUpTo(10, 15, 3);

  assert CommonDivsUpTo(10, 15, 5) == CommonDivsUpTo(10, 15, 4) + [5];
  assert CommonDivsUpTo(10, 15, 5) == [1, 5];

  assert CommonDivsUpTo(10, 15, 6) == CommonDivsUpTo(10, 15, 5);
  assert CommonDivsUpTo(10, 15, 7) == CommonDivsUpTo(10, 15, 6);
  assert CommonDivsUpTo(10, 15, 8) == CommonDivsUpTo(10, 15, 7);
  assert CommonDivsUpTo(10, 15, 9) == CommonDivsUpTo(10, 15, 8);
  assert CommonDivsUpTo(10, 15, 10) == CommonDivsUpTo(10, 15, 9);

  assert CommonDivsUpTo(10, 15, 10) == [1, 5];
}

lemma CommonDivisors_10_20()
  ensures commonDivisors(10, 20) == [1, 2, 5, 10]
{
  assert MinNat(10, 20) == 10;
  assert commonDivisors(10, 20) == CommonDivsUpTo(10, 20, 10);

  assert CommonDivsUpTo(10, 20, 0) == [];
  assert CommonDivsUpTo(10, 20, 1) == CommonDivsUpTo(10, 20, 0) + [1];
  assert CommonDivsUpTo(10, 20, 1) == [1];

  assert CommonDivsUpTo(10, 20, 2) == CommonDivsUpTo(10, 20, 1) + [2];
  assert CommonDivsUpTo(10, 20, 2) == [1, 2];

  assert CommonDivsUpTo(10, 20, 3) == CommonDivsUpTo(10, 20, 2);
  assert CommonDivsUpTo(10, 20, 4) == CommonDivsUpTo(10, 20, 3);

  assert CommonDivsUpTo(10, 20, 5) == CommonDivsUpTo(10, 20, 4) + [5];
  assert CommonDivsUpTo(10, 20, 5) == [1, 2, 5];

  assert CommonDivsUpTo(10, 20, 6) == CommonDivsUpTo(10, 20, 5);
  assert CommonDivsUpTo(10, 20, 7) == CommonDivsUpTo(10, 20, 6);
  assert CommonDivsUpTo(10, 20, 8) == CommonDivsUpTo(10, 20, 7);
  assert CommonDivsUpTo(10, 20, 9) == CommonDivsUpTo(10, 20, 8);

  assert CommonDivsUpTo(10, 20, 10) == CommonDivsUpTo(10, 20, 9) + [10];
  assert CommonDivsUpTo(10, 20, 10) == [1, 2, 5, 10];
}

lemma CommonDivisors_4_6()
  ensures commonDivisors(4, 6) == [1, 2]
{
  assert MinNat(4, 6) == 4;
  assert commonDivisors(4, 6) == CommonDivsUpTo(4, 6, 4);

  assert CommonDivsUpTo(4, 6, 0) == [];
  assert CommonDivsUpTo(4, 6, 1) == CommonDivsUpTo(4, 6, 0) + [1];
  assert CommonDivsUpTo(4, 6, 1) == [1];

  assert CommonDivsUpTo(4, 6, 2) == CommonDivsUpTo(4, 6, 1) + [2];
  assert CommonDivsUpTo(4, 6, 2) == [1, 2];

  assert CommonDivsUpTo(4, 6, 3) == CommonDivsUpTo(4, 6, 2);
  assert CommonDivsUpTo(4, 6, 4) == CommonDivsUpTo(4, 6, 3);

  assert CommonDivsUpTo(4, 6, 4) == [1, 2];
}

lemma SumSeq_1_5()
  ensures SumSeq([1, 5]) == 6
{
}

lemma SumSeq_1_2_5_10()
  ensures SumSeq([1, 2, 5, 10]) == 18
{
}

lemma SumSeq_1_2()
  ensures SumSeq([1, 2]) == 3
{
}

// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumSeq(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= MinNat(a, b) + 1
    invariant sum == SumSeq(CommonDivsUpTo(a, b, i - 1))
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
      SumSeqAppendOne(CommonDivsUpTo(a, b, i - 1), i);
      assert CommonDivsUpTo(a, b, i) == CommonDivsUpTo(a, b, i - 1) + [i];
      assert sum == SumSeq(CommonDivsUpTo(a, b, i));
    } else {
      assert CommonDivsUpTo(a, b, i) == CommonDivsUpTo(a, b, i - 1);
      assert sum == SumSeq(CommonDivsUpTo(a, b, i));
    }
    i := i + 1;
  }
  assert i == MinNat(a, b) + 1;
  assert sum == SumSeq(CommonDivsUpTo(a, b, MinNat(a, b)));
  assert commonDivisors(a, b) == CommonDivsUpTo(a, b, MinNat(a, b));
}

// Test cases checked statically
method SumOfCommonDivisorsTest(){
  var out1 := SumOfCommonDivisors(10, 15);
  CommonDivisors_10_15();
  assert commonDivisors(10, 15) == [1, 5];
  SumSeq_1_5();
  assert out1 == 6;
  
  var out2 := SumOfCommonDivisors(10, 20);
  CommonDivisors_10_20();
  assert commonDivisors(10, 20) == [1, 2, 5, 10];
  SumSeq_1_2_5_10();
  assert out2 == 18;
  
  var out3 := SumOfCommonDivisors(4,6);
  CommonDivisors_4_6();
  assert commonDivisors(4, 6) == [1, 2];
  SumSeq_1_2();
  assert out3 == 3;

  // @invalid: var out4 := SumOfCommonDivisors(0, 1); 
  // @invalid: var out5 := SumOfCommonDivisors(1, 0); 
  // @invalid: var out6 := SumOfCommonDivisors(0, 0); 
}
