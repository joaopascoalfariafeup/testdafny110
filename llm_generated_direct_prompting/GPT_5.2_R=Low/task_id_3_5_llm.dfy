// Checks if a natural number greater than 1 is non-prime.
method IsNonPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result <==> (exists d: int :: 2 <= d <= n/2 && n % d == 0)
{
  for i := 2 to n/2 + 1
    invariant 2 <= i <= n/2 + 1
    invariant forall d: int :: 2 <= d < i ==> n % d != 0
  {
    if n % i == 0 {
      assert 2 <= i <= n/2;
      assert n % i == 0;
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
  assert res2;

  var res3 := IsNonPrime(35);
  assert res3;
}

