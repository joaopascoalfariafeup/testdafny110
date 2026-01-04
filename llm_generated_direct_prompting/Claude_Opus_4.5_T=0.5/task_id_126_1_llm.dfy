// Returns the sum of the common divisors of two positive integers.

ghost function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  commonDivisorsUpTo(a, b, if a <= b then a else b)
}

ghost function commonDivisorsUpTo(a: nat, b: nat, n: nat): seq<nat>
  requires a > 0 && b > 0
{
  if n == 0 then []
  else if a % n == 0 && b % n == 0 then commonDivisorsUpTo(a, b, n - 1) + [n]
  else commonDivisorsUpTo(a, b, n - 1)
}

ghost function sumSeq(s: seq<nat>): nat
{
  if |s| == 0 then 0
  else s[|s| - 1] + sumSeq(s[..|s| - 1])
}

ghost function sumOfCommonDivisorsUpTo(a: nat, b: nat, n: nat): nat
  requires a > 0 && b > 0
{
  if n == 0 then 0
  else if a % n == 0 && b % n == 0 then n + sumOfCommonDivisorsUpTo(a, b, n - 1)
  else sumOfCommonDivisorsUpTo(a, b, n - 1)
}

lemma SumSeqCommonDivisors(a: nat, b: nat, n: nat)
  requires a > 0 && b > 0
  ensures sumSeq(commonDivisorsUpTo(a, b, n)) == sumOfCommonDivisorsUpTo(a, b, n)
{
  if n == 0 {
  } else if a % n == 0 && b % n == 0 {
    SumSeqCommonDivisors(a, b, n - 1);
  } else {
    SumSeqCommonDivisors(a, b, n - 1);
  }
}

method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == sumSeq(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= (if a <= b then a else b) + 1
    invariant sum == sumOfCommonDivisorsUpTo(a, b, i - 1)
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
  var minAB := if a <= b then a else b;
  assert i > a || i > b;
  assert i - 1 == minAB;
  SumSeqCommonDivisors(a, b, minAB);
}





// Test cases checked statically
method SumOfCommonDivisorsTest(){
  var out1 := SumOfCommonDivisors(10, 15);
  assert commonDivisorsUpTo(10, 15, 4) == [1];
  assert commonDivisorsUpTo(10, 15, 5) == [1, 5];
  assert commonDivisors(10, 15) == [1, 5];
  assert out1 == 6;
  
  var out2 := SumOfCommonDivisors(10, 20);
  assert commonDivisorsUpTo(10, 20, 1) == [1];
  assert commonDivisorsUpTo(10, 20, 2) == [1, 2];
  assert commonDivisorsUpTo(10, 20, 5) == [1, 2, 5];
  assert commonDivisorsUpTo(10, 20, 10) == [1, 2, 5, 10];
  assert commonDivisors(10, 20) == [1, 2, 5, 10];
  assert out2 == 18;
  
  var out3 := SumOfCommonDivisors(4,6);
  assert commonDivisorsUpTo(4, 6, 1) == [1];
  assert commonDivisorsUpTo(4, 6, 2) == [1, 2];
  assert commonDivisorsUpTo(4, 6, 4) == [1, 2];
  assert commonDivisors(4, 6) == [1, 2];
  assert out3 == 3;

  // @invalid: var out4 := SumOfCommonDivisors(0, 1); 
  // @invalid: var out5 := SumOfCommonDivisors(1, 0); 
  // @invalid: var out6 := SumOfCommonDivisors(0, 0); 

}
