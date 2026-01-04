// Checks if a natural number greater than 1 is non-prime.
ghost predicate HasDivisorInRange(n: nat, lo: nat, hi: nat)
{
  exists i :: lo <= i < hi && n % i == 0
}

method IsNonPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result <==> HasDivisorInRange(n, 2, n/2 + 1)
{
  for i := 2 to n/2 + 1
    invariant !HasDivisorInRange(n, 2, i)
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
  assert !HasDivisorInRange(2, 2, 2);
  assert !res1;

  var res2 := IsNonPrime(10);
  assert 10 % 2 == 0;
  assert HasDivisorInRange(10, 2, 6);
  assert res2;

  var res3 := IsNonPrime(35);
  assert 35 % 5 == 0;
  assert HasDivisorInRange(35, 2, 18);
  assert res3;
}

