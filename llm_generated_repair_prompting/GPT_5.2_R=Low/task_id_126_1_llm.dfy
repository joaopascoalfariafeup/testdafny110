// Auxiliary specification functions

function MinNat(a: nat, b: nat): nat {
  if a <= b then a else b
}

function {:fuel 10} CommonDivsUpTo(a: nat, b: nat, n: nat): seq<nat> {
  if n == 0 then
    []
  else
    if a % n == 0 && b % n == 0 then CommonDivsUpTo(a, b, n - 1) + [n]
    else CommonDivsUpTo(a, b, n - 1)
}

function {:fuel 10} commonDivisors(a: nat, b: nat): seq<nat> {
  CommonDivsUpTo(a, b, MinNat(a, b))
}

function {:fuel 20} SumSeq(s: seq<nat>): nat {
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

lemma SumSeqAppendOne(s: seq<nat>, x: nat)
  ensures SumSeq(s + [x]) == SumSeq(s) + x
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
  assert commonDivisors(10, 15) == [1, 5];
  assert out1 == 6;
  
  var out2 := SumOfCommonDivisors(10, 20);
  assert commonDivisors(10, 20) == [1, 2, 5, 10];
  assert out2 == 18;
  
  var out3 := SumOfCommonDivisors(4,6);
  assert commonDivisors(4, 6) == [1, 2];
  assert out3 == 3;

  // @invalid: var out4 := SumOfCommonDivisors(0, 1); 
  // @invalid: var out5 := SumOfCommonDivisors(1, 0); 
  // @invalid: var out6 := SumOfCommonDivisors(0, 0); 

}
