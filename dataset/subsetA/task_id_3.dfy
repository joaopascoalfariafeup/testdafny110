// Checks if a natural number greater than 1 is non-prime.
method IsNonPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result <==> exists k :: 1 < k < n && n % k == 0
{
  for i := 2 to n/2 + 1
    invariant ! exists k :: 1 < k < i && n % k == 0
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
  assert 10 % 2 == 0; // proof helper (example)
  assert res2;

  var res3 := IsNonPrime(35);
  assert 35 % 5 == 0; // proof helper (example)
  assert res3;
}
