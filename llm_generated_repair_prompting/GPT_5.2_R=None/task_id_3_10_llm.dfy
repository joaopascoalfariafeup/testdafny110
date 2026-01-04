// Arithmetic lemma used at loop exit
lemma RangeLeImpliesLt(j: nat, n: nat)
  requires 2 <= j <= n/2 + 1
  ensures j < n/2 + 2
{
  // since j <= n/2+1, we have j < n/2+2
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

  // At loop exit, found is still false
  assert !found;

  // At loop exit we know i == n/2+2 (from the for-loop bounds), so we can use the invariant
  // !found ==> (forall j :: 2 <= j < i ==> n%j != 0)
  assert forall t:nat :: 2 <= t < n/2 + 2 ==> n % t != 0 by {
    forall t:nat | 2 <= t < n/2 + 2
      ensures n % t != 0
    {
      // Here, i == n/2+2 at loop exit, so t satisfies 2 <= t < i, hence invariant gives n%t != 0.
    }
  }

  // From that, in particular, all candidates up to n/2+1 are non-divisors
  assert forall j:nat :: 2 <= j <= n/2 + 1 ==> n % j != 0 by {
    forall j:nat | 2 <= j <= n/2 + 1
      ensures n % j != 0
    {
      RangeLeImpliesLt(j, n);
      assert j < n/2 + 2;
      assert n % j != 0;
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
