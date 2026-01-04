// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonDivisorsSeq(a, b)
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= a + 1 && i <= b + 1
    invariant sum == SumCommonDivisorsSeqUpTo(a, b, i - 1)
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
}

ghost function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
  ensures forall d :: d in commonDivisors(a, b) ==> (a % d == 0 && b % d == 0)
  ensures forall d :: 1 <= d <= a && d <= b && a % d == 0 && b % d == 0 ==> d in commonDivisors(a, b)
{
  if a == 0 || b == 0 then []
  else var s := commonDivisors(a, b - 1);
       if b <= a && a % b == 0 && b % b == 0 then s + [b] else s
} by method {
  var res: seq<nat> := [];
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= a + 1 && i <= b + 1
    invariant forall d :: d in res ==> (a % d == 0 && b % d == 0)
    invariant forall d :: 1 <= d < i && a % d == 0 && b % d == 0 ==> d in res
  {
    if a % i == 0 && b % i == 0 {
      res := res + [i];
    }
    i := i + 1;
  }
  return res;
}

ghost function SumCommonDivisorsSeq(a: nat, b: nat): nat
  requires a > 0 && b > 0
  ensures SumCommonDivisorsSeq(a, b) == SumSeq(commonDivisors(a, b))
{
  SumSeq(commonDivisors(a, b))
}

ghost function SumCommonDivisorsSeqUpTo(a: nat, b: nat, n: nat): nat
  requires a > 0 && b > 0
  requires n <= a && n <= b
  ensures SumCommonDivisorsSeqUpTo(a, b, n) == SumSeq(commonDivisorsUpTo(a, b, n))
{
  SumSeq(commonDivisorsUpTo(a, b, n))
}

ghost function commonDivisorsUpTo(a: nat, b: nat, n: nat): seq<nat>
  requires a > 0 && b > 0
  requires n <= a && n <= b
  ensures forall d :: d in commonDivisorsUpTo(a, b, n) ==> (a % d == 0 && b % d == 0 && d <= n)
  ensures forall d :: 1 <= d <= n && a % d == 0 && b % d == 0 ==> d in commonDivisorsUpTo(a, b, n)
{
  if n == 0 then []
  else var s := commonDivisorsUpTo(a, b, n - 1);
       if a % n == 0 && b % n == 0 then s + [n] else s
}

ghost function SumSeq(s: seq<nat>): nat {
  if |s| == 0 then 0 else s[|s| - 1] + SumSeq(s[..|s| - 1])
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
