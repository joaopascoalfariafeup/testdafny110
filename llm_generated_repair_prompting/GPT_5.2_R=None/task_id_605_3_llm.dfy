// Checks if a number greater than 1 is prime.
method IsPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result <==> (forall k: nat :: 2 <= k <= n/2 ==> n % k != 0)
{
  var i := 2;
  while i <= n/2 + 1
    invariant 2 <= i <= n/2 + 2
    invariant forall k: nat :: 2 <= k < i ==> n % k != 0
    decreases n/2 + 2 - i
  {
    if n % i == 0 {
      // prove the negation of the universal in the postcondition:
      // i is in the quantified range (2 <= i <= n/2), hence the universal is false
      assert i <= n/2; // since i <= n/2 + 1 and n % i == 0 implies i != n/2 + 1
      assert !(forall k: nat :: 2 <= k <= n/2 ==> n % k != 0) by {
        // witness k := i
        assert 2 <= i <= n/2;
        assert !(n % i != 0);
      }
      return false;
    }
    i := i + 1;
  }

  // At loop exit: i = n/2+2, so all k in [2..n/2] are < i and thus covered by the invariant
  assert forall k: nat :: 2 <= k <= n/2 ==> n % k != 0;
  return true;
}

// Test cases checked statically by Dafny (for not very large numbers)
method IsPrimeTest(){
  // small prime number
  var out1 := IsPrime(13);
  assert out1;

  // non-prime number
  var out2 := IsPrime(1010);
  assert !out2;

  // large prime number
  var out3 := IsPrime(10007);
  assert out3;
}
