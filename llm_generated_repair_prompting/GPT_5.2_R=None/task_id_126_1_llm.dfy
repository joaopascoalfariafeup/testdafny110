// Returns the sum of the common divisors of two positive integers.

ghost predicate Divides(d: nat, x: nat)
{
  d > 0 && x % d == 0
}

ghost function {:fuel 0} SumCommonDivisorsUpTo(a: nat, b: nat, n: nat): nat
  requires a > 0 && b > 0
  requires n <= a + b + 1
{
  if n == 0 then 0
  else
    SumCommonDivisorsUpTo(a, b, n - 1) +
    (if Divides(n, a) && Divides(n, b) then n else 0)
}

method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonDivisorsUpTo(a, b, if a <= b then a else b)
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i
    invariant sum == SumCommonDivisorsUpTo(a, b, i - 1)
    decreases (if a <= b then a else b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
  assert i == (if a <= b then a else b) + 1;
  assert sum == SumCommonDivisorsUpTo(a, b, if a <= b then a else b);
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
