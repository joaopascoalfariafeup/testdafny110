ghost function Divides(x: nat, d: nat): bool
  requires d > 0
{
  x % d == 0
}

ghost function {:fuel 0} SumSeq(s: seq<nat>): nat
{
  if |s| == 0 then 0 else s[|s|-1] + SumSeq(s[..|s|-1])
}

ghost function {:fuel 1} CommonDivisorsUpTo(a: nat, b: nat, n: nat): seq<nat>
{
  if n == 0 then []
  else
    var s := CommonDivisorsUpTo(a, b, n-1);
    if Divides(a, n) && Divides(b, n) then s + [n] else s
}

ghost function commonDivisors(a: nat, b: nat): seq<nat>
{
  CommonDivisorsUpTo(a, b, if a <= b then a else b)
}

ghost function {:fuel 1} SumCommonDivisorsUpTo(a: nat, b: nat, n: nat): nat
{
  SumSeq(CommonDivisorsUpTo(a, b, n))
}

// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonDivisorsUpTo(a, b, if a <= b then a else b)
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i
    invariant sum == SumCommonDivisorsUpTo(a, b, i-1)
    decreases (if a <= b then a else b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
      assert Divides(a, i) && Divides(b, i);
      assert CommonDivisorsUpTo(a, b, i) == CommonDivisorsUpTo(a, b, i-1) + [i];
      assert SumCommonDivisorsUpTo(a, b, i) == SumCommonDivisorsUpTo(a, b, i-1) + i;
    } else {
      assert !(Divides(a, i) && Divides(b, i));
      assert CommonDivisorsUpTo(a, b, i) == CommonDivisorsUpTo(a, b, i-1);
      assert SumCommonDivisorsUpTo(a, b, i) == SumCommonDivisorsUpTo(a, b, i-1);
    }
    i := i + 1;
  }
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
