function Min(a: nat, b: nat): nat {
  if a <= b then a else b
}

function CommonDivides(a: nat, b: nat, k: nat): bool {
  k > 0 && a % k == 0 && b % k == 0
}

function SumSeq(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

function commonDivisorsUpTo(a: nat, b: nat, n: nat): seq<nat>
  decreases n
{
  if n == 0 then []
  else commonDivisorsUpTo(a, b, n - 1) + (if CommonDivides(a, b, n) then [n] else [])
}

function commonDivisors(a: nat, b: nat): seq<nat> {
  commonDivisorsUpTo(a, b, Min(a, b))
}

function SumCommonUpTo(a: nat, b: nat, n: nat): nat
  decreases n
{
  if n == 0 then 0
  else SumCommonUpTo(a, b, n - 1) + (if CommonDivides(a, b, n) then n else 0)
}

lemma SumCommonUpTo_SumSeqCommonDivisorsUpTo(a: nat, b: nat, n: nat)
  ensures SumCommonUpTo(a, b, n) == SumSeq(commonDivisorsUpTo(a, b, n))
  decreases n
{
  if n == 0 {
  } else {
    SumCommonUpTo_SumSeqCommonDivisorsUpTo(a, b, n - 1);
  }
}

// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonUpTo(a, b, Min(a, b))
  ensures sum == SumSeq(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= Min(a, b) + 1
    invariant sum == SumCommonUpTo(a, b, i - 1)
    decreases Min(a, b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }

  SumCommonUpTo_SumSeqCommonDivisorsUpTo(a, b, Min(a, b));
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
