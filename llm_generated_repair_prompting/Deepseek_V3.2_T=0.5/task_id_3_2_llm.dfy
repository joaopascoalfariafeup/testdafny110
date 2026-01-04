// Checks if a natural number greater than 1 is non-prime.
method IsNonPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result == exists i :: 2 <= i <= n/2 && n % i == 0
{
  for i := 2 to n/2 + 1
    invariant forall k :: 2 <= k < i ==> n % k != 0
  {
    if n % i == 0 {
      return true;
    }
  }
  return false;
}

// Test cases checked statically.
method IsNonPrimeTest(){
  var res1 := IsNonPrime(2);
  assert !res1;

  var res2 := IsNonPrime(10);
  // Helper assertion to verify that 10 is non-prime
  assert 10 % 2 == 0;
  assert res2;

  var res3 := IsNonPrime(35);
  // Helper assertion to verify that 35 is non-prime
  assert 35 % 5 == 0;
  assert res3;
}


