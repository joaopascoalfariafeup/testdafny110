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
      // i is in the quantified range [2..n/2], hence the universal is false
      // (the loop never checks n/2+1 since n%(n/2+1) cannot be 0 for n>1)
      assert i <= n/2 by {
        if i == n/2 + 1 {
          // show contradiction from n % (n/2+1) == 0
          // let q = n/(n/2+1), then q must be 1, hence remainder is n-(n/2+1) != 0
          var d := n/2 + 1;
          assert d > 0;
          assert d <= n by {  // since n >= 2, n/2+1 <= n
            assert n >= 2;
          }
          assert n / d == 1 by {
            // Because d > n/2 and d <= n, the quotient is 1
            assert d > n/2;
            assert n / d >= 1; // from d <= n and d > 0
            assert n / d <= 1 by {
              // if it were >=2 then n >= 2*d > n, contradiction
              if n / d >= 2 {
                assert n >= 2 * d;
                assert 2 * d > n by {
                  assert d > n/2;
                }
              }
            }
          }
          assert n % d == n - d by {
            // with quotient 1, remainder is n - d
            assert n == (n / d) * d + (n % d);
            assert n / d == 1;
          }
          assert n - d != 0 by {
            // n - (n/2+1) = n - n/2 - 1 >= 1-?; for n>1 it's positive
            assert n >= 2;
          }
          assert false; // contradicts n % i == 0 when i==d
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
  assert !out2;

  // large prime number
  var out3 := IsPrime(10007);
  assert out3;
}
