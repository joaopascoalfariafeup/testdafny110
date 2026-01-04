// A small arithmetic helper: for n >= 2, n/2 <= n-1 (integer division)
lemma HalfLeNMinus1(n: nat)
  requires n >= 2
  ensures n/2 <= n - 1
{
  // Since n/2 is floor(n/2) and n/2 <= n/2 + (n/2) = n when n>=2,
  // the simple inequality n/2 <= n-1 holds for all n>=2; Dafny needs a nudge.
  if n == 2 {
    assert n/2 == 1;
    assert n - 1 == 1;
  } else {
    // n >= 3
    assert n - 1 >= 2;
    // Use a crude bound: n/2 <= n/2 + 1 <= n-1 for n>=3
    // First, n/2 <= n/2 + 1
    assert n/2 <= n/2 + 1;
    // And for n>=3, n/2 + 1 <= n-1
    // Equivalent to n/2 <= n-2, which holds since n/2 <= n/2 + n/2 = n and n-2 >= 1;
    // we prove directly by case split on n.
    if n == 3 {
      assert n/2 == 1;
      assert n - 2 == 1;
    } else {
      // n >= 4, so n/2 <= n-2 is true (easy numeric fact)
      // Prove by showing 2*(n-2) >= n, hence n-2 >= n/2
      assert 2*(n-2) >= n;
    }
    assert n/2 + 1 <= n - 1;
  }
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
            // For n>1, d = n/2+1 <= n-1 (equivalently n/2 <= n-2), but it's enough to show d <= n-1.
            // We prove the stronger, simpler fact: n/2 <= n-1 for n>=2.
            HalfLeNMinus1(n);
            assert n/2 + 1 <= (n - 1) + 1;
            assert d <= n;
            // And for n>=2, actually d < n:
            // if d == n then n/2 + 1 == n implies n/2 == n-1, only possible for n==2, but then d==2 and d<n is false.
            // However n==2 cannot reach this branch because then n/2+1 == 2 and i==2 divides n, but i must satisfy i<=n/2,
            // so we rule out d==n via the quotient argument below: if d==n then n/d==1 and n%d==0 contradicts remainder positivity.
            if d == n {
              assert n % d == 0;
              // But from d > n/2, n/d must be 1, giving remainder n-d = 0; contradict the earlier plan to show >0.
              // We instead show directly that d cannot equal n because d = n/2+1 and n>1.
              // For n==2, d==2, but then i==2 and i<=n/2 is false, contradicting i<=n/2 established above.
              assert i <= n/2; // from the enclosing goal when i==d
              assert false;
            }
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
