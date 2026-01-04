// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == Sum(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i
    invariant sum == Sum(commonDivisorsUpTo(a, b, i))
    decreases (if a <= b then a else b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
  assert i == (if a <= b then a else b) + 1;
  assert commonDivisorsUpTo(a, b, i) == commonDivisors(a, b);
}

ghost function Sum(s: seq<nat>): nat
{
  if |s| == 0 then 0 else s[|s|-1] + Sum(s[..|s|-1])
}

ghost function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  commonDivisorsUpTo(a, b, (if a <= b then a else b) + 1)
}

ghost function commonDivisorsUpTo(a: nat, b: nat, i: nat): seq<nat>
  requires a > 0 && b > 0
{
  if i <= 1 then []
  else
    commonDivisorsUpTo(a, b, i - 1) +
    (if a % (i - 1) == 0 && b % (i - 1) == 0 then [i - 1] else [])
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
