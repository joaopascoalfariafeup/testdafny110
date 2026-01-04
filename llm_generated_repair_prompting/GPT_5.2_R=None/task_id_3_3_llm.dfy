// Checks if a natural number greater than 1 is non-prime.
method IsNonPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result <==> (exists i: nat :: 2 <= i <= n/2 + 1 && n % i == 0)
{
  for i := 2 to n/2 + 1
    invariant 2 <= i <= n/2 + 2
    invariant forall j:nat :: 2 <= j < i ==> n % j != 0
  {
    if n % i == 0 {
      // witness i for the existential
      assert 2 <= i <= n/2 + 1 && n % i == 0;
      return true;
    }
  }
  // no divisor found in [2 .. n/2+1]
  // At loop exit, i == n/2+2, so the invariant gives the needed range
  assert forall j:nat :: 2 <= j <= n/2 + 1 ==> n % j != 0 by {
    assert forall j:nat :: 2 <= j < (n/2 + 2) ==> n % j != 0;
  }
  assert !(exists j:nat :: 2 <= j <= n/2 + 1 && n % j == 0);
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
