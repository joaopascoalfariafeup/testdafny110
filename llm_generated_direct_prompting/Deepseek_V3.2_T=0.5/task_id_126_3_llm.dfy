// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonDivisorsSeq(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= a + 1 && i <= b + 1
    invariant sum == SumCommonDivisorsSeq(commonDivisorsUpTo(a, b, i - 1))
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
}

ghost function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
  ensures forall d :: d in commonDivisors(a, b) ==> d > 0 && a % d == 0 && b % d == 0
  ensures forall d :: 1 <= d <= a && d <= b && a % d == 0 && b % d == 0 ==> d in commonDivisors(a, b)
{
  if a == 0 || b == 0 then []
  else var s := [];
    for d : nat := 1 to a + 1
      invariant d == 0 ==> s == []
      invariant d > 0 ==> forall x :: x in s ==> 1 <= x < d && a % x == 0 && b % x == 0
      invariant d > 0 ==> forall x :: 1 <= x < d && a % x == 0 && b % x == 0 ==> x in s
    {
      if d <= a && d <= b && a % d == 0 && b % d == 0 {
        s := s + [d];
      }
    }
    s
}

ghost function commonDivisorsUpTo(a: nat, b: nat, limit: nat): seq<nat>
  requires a > 0 && b > 0
  ensures forall d :: d in commonDivisorsUpTo(a, b, limit) ==> d > 0 && d <= limit && a % d == 0 && b % d == 0
  ensures forall d :: 1 <= d <= limit && d <= a && d <= b && a % d == 0 && b % d == 0 ==> d in commonDivisorsUpTo(a, b, limit)
{
  if limit == 0 then []
  else var s := [];
    for d : nat := 1 to limit + 1
      invariant d == 0 ==> s == []
      invariant d > 0 ==> forall x :: x in s ==> 1 <= x < d && a % x == 0 && b % x == 0
      invariant d > 0 ==> forall x :: 1 <= x < d && a % x == 0 && b % x == 0 ==> x in s
    {
      if d <= a && d <= b && a % d == 0 && b % d == 0 {
        s := s + [d];
      }
    }
    s
}

ghost function SumCommonDivisorsSeq(s: seq<nat>): nat
{
  if |s| == 0 then 0
  else s[|s| - 1] + SumCommonDivisorsSeq(s[..|s| - 1])
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
