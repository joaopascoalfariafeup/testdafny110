
// Function to get the common divisors of two numbers
ghost function commonDivisors(a: nat, b: nat): seq<nat>
{
  [k in nat | 0 < k <= a && 0 < k <= b && a % k == 0 && b % k == 0]
}

// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  ensures forall k :: 0 < k <= a && 0 < k <= b && a % k == 0 && b % k == 0 ==> k <= sum
  ensures forall k :: 0 < k <= sum ==> (k <= a && k <= b && a % k == 0 && b % k == 0)
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant sum == i - 1
    invariant forall k :: 0 < k < i && a % k == 0 && b % k == 0 ==> k <= sum
    invariant forall k :: 0 < k <= sum ==> (k < i && a % k == 0 && b % k == 0)
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
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

