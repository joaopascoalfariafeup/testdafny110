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

// ------------------------
// Arithmetic proof helpers
// ------------------------

lemma EuclidUnique(b: nat, q1: nat, r1: nat, q2: nat, r2: nat)
  requires b > 0
  requires r1 < b && r2 < b
  requires b * q1 + r1 == b * q2 + r2
  ensures q1 == q2 && r1 == r2
{
  // Work in integers for subtraction/ordering
  var B: int := b as int;
  var Q1: int := q1 as int;
  var Q2: int := q2 as int;
  var R1: int := r1 as int;
  var R2: int := r2 as int;

  assert B > 0;
  assert 0 <= R1 < B;
  assert 0 <= R2 < B;
  assert B * Q1 + R1 == B * Q2 + R2;
  assert B * (Q1 - Q2) == R2 - R1;

  if q1 < q2 {
    assert Q1 - Q2 <= -1;
    assert B * (Q1 - Q2) <= -B;
    assert R2 - R1 > -B; // since R2 - R1 >= -(B-1)
    assert B * (Q1 - Q2) != R2 - R1;
  } else if q2 < q1 {
    assert Q1 - Q2 >= 1;
    assert B * (Q1 - Q2) >= B;
    assert R2 - R1 < B; // since R2 - R1 <= B-1
    assert B * (Q1 - Q2) != R2 - R1;
  } else {
    // q1 == q2
  }

  assert q1 == q2;
  assert B * (Q1 - Q2) == 0;
  assert R2 - R1 == 0;
  assert r1 == r2;
}

lemma DivModFromQR(a: nat, b: nat, q: nat, r: nat)
  requires b > 0
  requires a == b * q + r
  requires r < b
  ensures a / b == q
  ensures a % b == r
{
  // Dafny's div/mod axiom:
  // a == (a / b) * b + a % b  and  a % b < b  when b > 0
  assert a == (a / b) * b + a % b;
  assert a % b < b;

  EuclidUnique(b, a / b, a % b, q, r);
}

lemma Mod_10_9()
  ensures 10 % 9 == 1
{
  assert 10 == 9 * 1 + 1;
  assert 1 < 9;
  DivModFromQR(10, 9, 1, 1);
}

lemma Mod_15_9()
  ensures 15 % 9 == 6
{
  assert 15 == 9 * 1 + 6;
  assert 6 < 9;
  DivModFromQR(15, 9, 1, 6);
}

lemma Mod_4_3()
  ensures 4 % 3 == 1
{
  assert 4 == 3 * 1 + 1;
  assert 1 < 3;
  DivModFromQR(4, 3, 1, 1);
}

lemma Mod_6_3()
  ensures 6 % 3 == 0
{
  assert 6 == 3 * 2 + 0;
  assert 0 < 3;
  DivModFromQR(6, 3, 2, 0);
}

// ------------------------
// Original lemmas/functions
// ------------------------

lemma CommonDivsUpToStep(a: nat, b: nat, n: nat)
  requires n > 0
  ensures CommonDivsUpTo(a, b, n) ==
            (if a % n == 0 && b % n == 0
             then CommonDivsUpTo(a, b, n - 1) + [n]
             else CommonDivsUpTo(a, b, n - 1))
{
}

lemma SumSeqUnfold(s: seq<nat>)
  requires |s| > 0
  ensures SumSeq(s) == SumSeq(s[..|s|-1]) + s[|s|-1]
{
}

lemma SumSeqAppendOne(s: seq<nat>, x: nat)
  ensures SumSeq(s + [x]) == SumSeq(s) + x
  decreases |s|
{
  if |s| == 0 {
  } else {
    SumSeqAppendOne(s[..|s|-1], x);
    assert s == s[..|s|-1] + [s[|s|-1]];
    assert s + [x] == (s[..|s|-1] + [s[|s|-1]]) + [x];
    assert (s[..|s|-1] + [s[|s|-1]]) + [x] == s[..|s|-1] + [s[|s|-1], x];
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
  assert MinNat(10, 15) == 10;
  assert commonDivisors(10, 15) == CommonDivsUpTo(10, 15, 10);

  assert CommonDivsUpTo(10, 15, (0 as nat)) == [];
  CommonDivsUpToStep(10, 15, 1);
  assert CommonDivsUpTo(10, 15, (1 as nat)) == CommonDivsUpTo(10, 15, (0 as nat)) + [1];
  assert CommonDivsUpTo(10, 15, (1 as nat)) == [1];

  CommonDivsUpToStep(10, 15, 2);
  assert CommonDivsUpTo(10, 15, (2 as nat)) == CommonDivsUpTo(10, 15, (1 as nat));
  CommonDivsUpToStep(10, 15, 3);
  assert CommonDivsUpTo(10, 15, (3 as nat)) == CommonDivsUpTo(10, 15, (2 as nat));
  CommonDivsUpToStep(10, 15, 4);
  assert CommonDivsUpTo(10, 15, (4 as nat)) == CommonDivsUpTo(10, 15, (3 as nat));

  CommonDivsUpToStep(10, 15, 5);
  assert CommonDivsUpTo(10, 15, (5 as nat)) == CommonDivsUpTo(10, 15, (4 as nat)) + [5];
  assert CommonDivsUpTo(10, 15, (5 as nat)) == [1, 5];

  CommonDivsUpToStep(10, 15, 6);
  assert CommonDivsUpTo(10, 15, (6 as nat)) == CommonDivsUpTo(10, 15, (5 as nat));
  CommonDivsUpToStep(10, 15, 7);
  assert CommonDivsUpTo(10, 15, (7 as nat)) == CommonDivsUpTo(10, 15, (6 as nat));
  CommonDivsUpToStep(10, 15, 8);
  assert CommonDivsUpTo(10, 15, (8 as nat)) == CommonDivsUpTo(10, 15, (7 as nat));

  // problematic step: n = 9
  Mod_10_9();
  assert 10 % 9 == 1;
  Mod_15_9();
  assert 15 % 9 == 6;
  assert !(10 % 9 == 0 && 15 % 9 == 0);
  CommonDivsUpToStep(10, 15, 9);
  assert CommonDivsUpTo(10, 15, (9 as nat)) == CommonDivsUpTo(10, 15, (8 as nat));

  CommonDivsUpToStep(10, 15, 10);
  assert CommonDivsUpTo(10, 15, (10 as nat)) == CommonDivsUpTo(10, 15, (9 as nat));

  assert CommonDivsUpTo(10, 15, (10 as nat)) == [1, 5];
}

lemma CommonDivisors_10_20()
  ensures commonDivisors(10, 20) == [1, 2, 5, 10]
{
  assert MinNat(10, 20) == 10;
  assert commonDivisors(10, 20) == CommonDivsUpTo(10, 20, 10);

  assert CommonDivsUpTo(10, 20, (0 as nat)) == [];
  CommonDivsUpToStep(10, 20, 1);
  assert CommonDivsUpTo(10, 20, (1 as nat)) == CommonDivsUpTo(10, 20, (0 as nat)) + [1];
  assert CommonDivsUpTo(10, 20, (1 as nat)) == [1];

  CommonDivsUpToStep(10, 20, 2);
  assert CommonDivsUpTo(10, 20, (2 as nat)) == CommonDivsUpTo(10, 20, (1 as nat)) + [2];
  assert CommonDivsUpTo(10, 20, (2 as nat)) == [1, 2];

  CommonDivsUpToStep(10, 20, 3);
  assert CommonDivsUpTo(10, 20, (3 as nat)) == CommonDivsUpTo(10, 20, (2 as nat));
  CommonDivsUpToStep(10, 20, 4);
  assert CommonDivsUpTo(10, 20, (4 as nat)) == CommonDivsUpTo(10, 20, (3 as nat));

  CommonDivsUpToStep(10, 20, 5);
  assert CommonDivsUpTo(10, 20, (5 as nat)) == CommonDivsUpTo(10, 20, (4 as nat)) + [5];
  assert CommonDivsUpTo(10, 20, (5 as nat)) == [1, 2, 5];

  CommonDivsUpToStep(10, 20, 6);
  assert CommonDivsUpTo(10, 20, (6 as nat)) == CommonDivsUpTo(10, 20, (5 as nat));
  CommonDivsUpToStep(10, 20, 7);
  assert CommonDivsUpTo(10, 20, (7 as nat)) == CommonDivsUpTo(10, 20, (6 as nat));
  CommonDivsUpToStep(10, 20, 8);
  assert CommonDivsUpTo(10, 20, (8 as nat)) == CommonDivsUpTo(10, 20, (7 as nat));
  CommonDivsUpToStep(10, 20, 9);
  assert CommonDivsUpTo(10, 20, (9 as nat)) == CommonDivsUpTo(10, 20, (8 as nat));

  CommonDivsUpToStep(10, 20, 10);
  assert CommonDivsUpTo(10, 20, (10 as nat)) == CommonDivsUpTo(10, 20, (9 as nat)) + [10];
  assert CommonDivsUpTo(10, 20, (10 as nat)) == [1, 2, 5, 10];
}

lemma CommonDivisors_4_6()
  ensures commonDivisors(4, 6) == [1, 2]
{
  assert MinNat(4, 6) == 4;
  assert commonDivisors(4, 6) == CommonDivsUpTo(4, 6, 4);

  assert CommonDivsUpTo(4, 6, (0 as nat)) == [];
  CommonDivsUpToStep(4, 6, 1);
  assert CommonDivsUpTo(4, 6, (1 as nat)) == CommonDivsUpTo(4, 6, (0 as nat)) + [1];
  assert CommonDivsUpTo(4, 6, (1 as nat)) == [1];

  CommonDivsUpToStep(4, 6, 2);
  assert CommonDivsUpTo(4, 6, (2 as nat)) == CommonDivsUpTo(4, 6, (1 as nat)) + [2];
  assert CommonDivsUpTo(4, 6, (2 as nat)) == [1, 2];

  // problematic step: n = 3
  Mod_4_3();
  assert 4 % 3 == 1;
  Mod_6_3();
  assert 6 % 3 == 0;
  assert !(4 % 3 == 0 && 6 % 3 == 0);
  CommonDivsUpToStep(4, 6, 3);
  assert CommonDivsUpTo(4, 6, (3 as nat)) == CommonDivsUpTo(4, 6, (2 as nat));

  CommonDivsUpToStep(4, 6, 4);
  assert CommonDivsUpTo(4, 6, (4 as nat)) == CommonDivsUpTo(4, 6, (3 as nat));

  assert CommonDivsUpTo(4, 6, (4 as nat)) == [1, 2];
}

lemma SumSeq_1_5()
  ensures SumSeq([1, 5]) == 6
{
  calc {
    SumSeq([1, 5]);
    == { SumSeqUnfold([1, 5]); }
    SumSeq([1]) + 5;
    == { SumSeqUnfold([1]); }
    (SumSeq([]) + 1) + 5;
    == { }
    (0 + 1) + 5;
    == { }
    6;
  }
}

lemma SumSeq_1_2_5_10()
  ensures SumSeq([1, 2, 5, 10]) == 18
{
  calc {
    SumSeq([1, 2, 5, 10]);
    == { SumSeqUnfold([1, 2, 5, 10]); }
    SumSeq([1, 2, 5]) + 10;
    == { SumSeqUnfold([1, 2, 5]); }
    (SumSeq([1, 2]) + 5) + 10;
    == { SumSeqUnfold([1, 2]); }
    ((SumSeq([1]) + 2) + 5) + 10;
    == { SumSeqUnfold([1]); }
    (((SumSeq([]) + 1) + 2) + 5) + 10;
    == { }
    (((0 + 1) + 2) + 5) + 10;
    == { }
    18;
  }
}

lemma SumSeq_1_2()
  ensures SumSeq([1, 2]) == 3
{
  calc {
    SumSeq([1, 2]);
    == { SumSeqUnfold([1, 2]); }
    SumSeq([1]) + 2;
    == { SumSeqUnfold([1]); }
    (SumSeq([]) + 1) + 2;
    == { }
    (0 + 1) + 2;
    == { }
    3;
  }
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
