// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
    ensures sum >= 0
    ensures sum == SumSeq(CommonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant i >= 1
    invariant sum == SumSeq(CommonDivisors(a, b)[0..i])
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
}

// Auxiliary function to generate a sequence of common divisors
function CommonDivisors(a: nat, b: nat): seq<nat> {
  [i: nat | 1 <= i <= min(a, b) && a % i == 0 && b % i == 0]
}

// Auxiliary function to sum the elements of a sequence
function SumSeq(s: seq<nat>): nat {
  if |s| == 0 then 0 else s[|s|-1] + SumSeq(s[..|s|-1])
}

// Test cases checked statically
method SumOfCommonDivisorsTest(){
  var out1 := SumOfCommonDivisors(10, 15);
  assert CommonDivisors(10, 15) == [1, 5];
  assert out1 == 6;
  
  var out2 := SumOfCommonDivisors(10, 20);
  assert CommonDivisors(10, 20) == [1, 2, 5, 10];
  assert out2 == 18;
  
  var out3 := SumOfCommonDivisors(4,6);
  assert CommonDivisors(4, 6) == [1, 2];
  assert out3 == 3;

  // @invalid: var out4 := SumOfCommonDivisors(0, 1); 
  // @invalid: var out5 := SumOfCommonDivisors(1, 0); 
  // @invalid: var out6 := SumOfCommonDivisors(0, 0); 

}
