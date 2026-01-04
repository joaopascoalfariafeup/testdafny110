// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == sumSeq(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  ghost var divisors : seq<int> := []; // helper, keeps track of the common divisors so far (ghost)
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= min(a, b) + 1
    invariant divisors == commonDivisors(a, b, i - 1)
    invariant sum == sumSeq(divisors)
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
      divisors := divisors + [i]; // helper
    }
    i := i + 1;
  }
}

// Auxiliary function that returns a list of common divisors of two positive integers
// 'a' and 'b', up to a maximum divisor 'd'.
ghost function {:fuel 4} commonDivisors(a: nat, b: nat, d: nat := min(a, b)): seq<nat> 
  ensures forall x :: x in commonDivisors(a, b, d) ==> IsCommonDivisor(x, a, b)
{
  if d == 0 then []
  else if IsCommonDivisor(d, a, b) then commonDivisors(a, b, d - 1) + [d]
  else commonDivisors(a, b, d - 1)
}

// Retrieves the minimum of two integers
ghost function min(a: int, b: int): int {
  if a < b then a else b
}

// Checks if 'd' is a common divisor of 'a' and 'b'
ghost predicate IsCommonDivisor(d: nat, a: nat, b: nat) {
  d > 0 && a % d == 0 && b % d == 0
}

// Auxiliary function that returns the sum of elements in a list
ghost function {:fuel 4} sumSeq(s: seq<int>): int {
  if |s| == 0 then 0 else s[|s|-1] + sumSeq(s[..|s|-1]) 
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