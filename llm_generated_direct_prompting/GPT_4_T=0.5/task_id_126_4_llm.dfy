// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  ensures sum == SumDivisors(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= a + 1 && 1 <= i <= b + 1
    invariant sum == SumDivisors(commonDivisors(a, b)[..i-1])
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
}

// Ghost function to calculate sum of divisors in a sequence
ghost function SumDivisors(s: seq<nat>): nat
{
  if |s| == 0 then 0 else s[|s|-1] + SumDivisors(s[..|s|-1])
}

// Ghost function to get common divisors of two numbers
ghost function commonDivisors(a: nat, b: nat): seq<nat>
{
  [i in nat | i <= a && i <= b && a % i == 0 && b % i == 0]
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
