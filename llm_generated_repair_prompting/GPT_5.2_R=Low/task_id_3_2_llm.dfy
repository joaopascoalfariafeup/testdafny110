// Checks if a natural number greater than 1 is non-prime.
method IsNonPrime(n: nat) returns (result: bool)
  requires n >= 2
  ensures result <==> (exists d:int :: 2 <= d <= n/2 && n % d == 0)
{
  for i := 2 to n/2 + 1
    invariant 2 <= i <= n/2 + 1
    invariant forall k:int :: 2 <= k < i ==> n % k != 0
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
  // Provide an explicit witness (d = 2) for the postcondition's existential
  assert (exists d:int :: d == 2 && 2 <= d <= 10/2 && 10 % d == 0);
  assert (exists d:int :: 2 <= d <= 10/2 && 10 % d == 0);
  assert res2;

  var res3 := IsNonPrime(35);
  // Provide an explicit witness (d = 5) for the postcondition's existential
  assert (exists d:int :: d == 5 && 2 <= d <= 35/2 && 35 % d == 0);
  assert (exists d:int :: 2 <= d <= 35/2 && 35 % d == 0);
  assert res3;
}
