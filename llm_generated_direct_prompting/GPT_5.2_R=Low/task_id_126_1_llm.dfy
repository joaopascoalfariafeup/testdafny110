function MinNat(a: nat, b: nat): nat {
  if a <= b then a else b
}

predicate IsCommonDivisor(d: nat, a: nat, b: nat) {
  d > 0 && a % d == 0 && b % d == 0
}

function commonDivisorsUpTo(n: nat, a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  if n == 0 then []
  else
    commonDivisorsUpTo(n - 1, a, b) +
    (if IsCommonDivisor(n, a, b) then [n] else [])
}

function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  commonDivisorsUpTo(MinNat(a, b), a, b)
}

function SumSeq(s: seq<nat>): nat {
  if |s| == 0 then 0
  else SumSeq(s[..|s|-1]) + s[|s|-1]
}

lemma SumSeqAppendSingleton(s: seq<nat>, x: nat)
  ensures SumSeq(s + [x]) == SumSeq(s) + x
{
  assert (s + [x])[..|(s + [x])| - 1] == s;
  assert (s + [x])[|(s + [x])| - 1] == x;
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
    invariant sum == SumSeq(commonDivisorsUpTo(i - 1, a, b))
    decreases MinNat(a, b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      assert IsCommonDivisor(i, a, b);
      SumSeqAppendSingleton(commonDivisorsUpTo(i - 1, a, b), i);
      sum := sum + i;
      assert sum == SumSeq(commonDivisorsUpTo(i, a, b));
    } else {
      assert !IsCommonDivisor(i, a, b);
      assert commonDivisorsUpTo(i, a, b) == commonDivisorsUpTo(i - 1, a, b) + [];
      assert SumSeq(commonDivisorsUpTo(i, a, b)) == SumSeq(commonDivisorsUpTo(i - 1, a, b));
      assert sum == SumSeq(commonDivisorsUpTo(i, a, b));
    }
    i := i + 1;
  }

  assert i == MinNat(a, b) + 1;
  assert sum == SumSeq(commonDivisorsUpTo(MinNat(a, b), a, b));
  assert sum == SumSeq(commonDivisors(a, b));
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
