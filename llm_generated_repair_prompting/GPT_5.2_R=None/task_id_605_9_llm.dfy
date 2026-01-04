// A small arithmetic helper: for n >= 2, n/2 <= n-1 (integer division)
lemma HalfLeNMinus1(n: nat)
  requires n >= 2
  ensures n/2 <= n - 1
{
  if n == 2 {
    assert n/2 == 1;
    assert n - 1 == 1;
  } else {
    assert n - 1 >= 2;
    assert n/2 <= n/2 + 1;
    if n == 3 {
      assert n/2 == 1;
      assert n - 2 == 1;
    } else {
      assert 2*(n-2) >= n;
    }
    assert n/2 + 1 <= n - 1;
  }
}

// Useful arithmetic fact: for n>=2, n/2 + 1 < n
lemma HalfPlus1LtN(n: nat)
  requires n >= 2
  ensures n/2 + 1 < n
{
  // From HalfLeNMinus1: n/2 <= n-1, so n/2+1 <= n. Show it's not equal.
  HalfLeNMinus1(n);
  if n/2 + 1 == n {
    // Then n/2 == n-1. This only happens for n==2, but then n/2+1 == 2 is not < n==2, contradiction with strictness we need.
    // Derive contradiction directly by case split.
    if n == 2 {
      assert n/2 == 1;
      assert n/2 + 1 == 2;
      assert false;
    } else if n == 3 {
      assert n/2 == 1;
      assert n/2 + 1 == 2;
      assert n == 3;
      assert 2 != 3;
      assert false;
    } else {
      // n >= 4: show n/2 <= n-2, hence n/2+1 <= n-1
      assert n >= 4;
      assert 2*(n-2) >= n;
      // (n-2) >= n/2
      assert n - 2 >= n/2;
      assert n/2 <= n - 2;
      assert n/2 + 1 <= (n - 2) + 1;
      assert n/2 + 1 <= n - 1;
      assert n - 1 < n;
      assert n/2 + 1 < n;
      return;
    }
  }
  // n/2+1 != n and n/2+1 <= n, so n/2+1 < n
  assert n/2 + 1 <= n;
  assert n/2 + 1 < n;
}

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
      // i is in the quantified range [2..n/2], since i==n/2+1 cannot divide n for n>1
      assert i <= n/2 by {
        if i == n/2 + 1 {
          var d := n/2 + 1;
          assert d > n/2;

          // If n == d*q then n >= 2*d would be needed for q >= 2, impossible since d > n/2.
          assert n / d <= 1 by {
            if n / d >= 2 {
              assert n >= (n / d) * d;
              assert (n / d) * d >= 2 * d;
              assert 2 * d > n by { assert d > n/2; }
            }
          }

          // Also d <= n, so quotient is at least 1; hence quotient must be 1.
          assert d <= n by {
            assert n >= 2;
          }
          assert n / d >= 1;
          assert n / d == 1;

          // Then remainder is n - d, which is positive since d = n/2+1 < n for n>1.
          assert d < n by {
            assert n >= 2;
            HalfPlus1LtN(n);
            assert d == n/2 + 1;
          }

          assert n == (n / d) * d + (n % d);
          assert n % d == n - d;
          assert n - d > 0 by { assert d < n; }
          assert n % d != 0;
          assert false; // contradicts n % i == 0 when i == d
        }
      }

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
  // Help Dafny: exhibit an explicit divisor within [2..n/2]
  assert 2 <= 2 <= 1010/2;
  assert 1010 % 2 == 0;
  assert !out2;

  // large prime number
  var out3 := IsPrime(10007);
  assert out3;
}
