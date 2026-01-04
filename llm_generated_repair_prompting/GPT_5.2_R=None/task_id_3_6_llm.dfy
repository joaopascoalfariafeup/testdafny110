// A tiny helper predicate used to avoid trigger warnings on quantifiers
ghost predicate LeToLt(j: nat, n: nat)
{
  2 <= j <= n/2 + 1 ==> j < n/2 + 2
}

// Checks if a natural number greater than 1 is non-prime.
method IsNonPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result <==> (exists i: nat :: 2 <= i <= n/2 + 1 && n % i == 0)
{
  var found := false;

  for i := 2 to n/2 + 1
    invariant 2 <= i <= n/2 + 2
    invariant found ==> (exists k:nat :: 2 <= k < i && n % k == 0)
    // If we have not returned yet, then no divisor has been seen so far
    invariant !found ==> (forall j:nat :: 2 <= j < i ==> n % j != 0)
  {
    if n % i == 0 {
      // witness i for the existential
      assert 2 <= i <= n/2 + 1 && n % i == 0;
      found := true;
      return true;
    }
  }

  // At loop exit, we have i == n/2 + 2, and found is still false
  assert !found;

  // From invariant with i == n/2+2 we get all candidates up to n/2+1 are non-divisors
  assert forall j:nat :: 2 <= j <= n/2 + 1 ==> n % j != 0 by {
    assert forall j:nat :: LeToLt(j, n); // avoids trigger warning
    assert forall j:nat :: 2 <= j <= n/2 + 1 ==> j < n/2 + 2 by {
      // prove the arithmetic fact directly for an arbitrary j
      forall j:nat | 2 <= j <= n/2 + 1
        ensures j < n/2 + 2
      {
      }
    }
    // now use the loop invariant (with i == n/2+2) to conclude n%j != 0
    assert forall j:nat :: 2 <= j <= n/2 + 1 ==> n % j != 0 by {
      forall j:nat | 2 <= j <= n/2 + 1
        ensures n % j != 0
      {
        assert j < n/2 + 2;
      }
    }
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
