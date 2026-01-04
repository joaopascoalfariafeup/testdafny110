// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

ghost function Product(s: seq<nat>): nat
{
  if |s| == 0 then 1 else Product(s[..|s|-1]) * s[|s|-1]
}

ghost predicate Nondecreasing(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate IsPrime(p: nat)
{
  p >= 2 && (forall k :: 2 <= k < p ==> p % k != 0)
}

ghost predicate NoDivisorsLessThan(m: nat, d: nat)
{
  forall k :: 2 <= k < d ==> m % k != 0
}

// Spec that matches the loop (trial division, nondecreasing factors)
// NOTE: We add a safe "div>n" base case so the function is total under its requires.
ghost function {:fuel 40} PFLoop(n: nat, div: nat): seq<nat>
  requires div >= 2
  requires n >= 1
  decreases n, if n <= 1 || div > n then 0 else n - div
{
  if n == 1 then []
  else if div > n then []
  else if n % div == 0 then [div] + PFLoop(n / div, div)
  else PFLoop(n, div + 1)
}

lemma SeqConcatAssoc<T>(a: seq<T>, b: seq<T>, c: seq<T>)
  ensures (a + b) + c == a + (b + c)
{
  calc {
    (a + b) + c;
    == a + (b + c);
  }
}

lemma {:isolate_assertions} DividesTransitiveNat(m: nat, d: nat, k: nat)
  requires d > 0
  requires k > 0
  requires m % d == 0
  requires d % k == 0
  ensures m % k == 0
{
  var q := m / d;
  var r := d / k;

  assert m == d * q;
  assert d == k * r;

  // Show m is a multiple of k
  calc {
    m;
    == d * q;
    == (k * r) * q;
    == k * (r * q);
  }
  assert m % k == 0;
}

lemma NoDivisorsLessThan_Step(m: nat, div: nat)
  requires div >= 2
  requires NoDivisorsLessThan(m, div)
  requires m % div != 0
  ensures NoDivisorsLessThan(m, div + 1)
{
  // Need: forall k :: 2 <= k < div+1 ==> m%k != 0
  forall k | 2 <= k < div + 1
    ensures m % k != 0
  {
    if k < div {
      // from NoDivisorsLessThan(m, div)
      assert m % k != 0;
    } else {
      assert k == div;
      assert m % k != 0;
    }
  }
}

lemma {:isolate_assertions} NoDivisorsLessThan_Divide(m: nat, d: nat)
  requires m > 1
  requires d >= 2
  requires m % d == 0
  requires NoDivisorsLessThan(m, d)
  ensures NoDivisorsLessThan(m / d, d)
{
  var q := m / d;
  assert m == d * q;

  // Need: forall k :: 2 <= k < d ==> (m/d)%k != 0
  forall k | 2 <= k < d
    ensures (m / d) % k != 0
  {
    if q % k == 0 {
      // q is a multiple of k, hence m = d*q is also a multiple of k
      var t := q / k;
      assert q == k * t by {
        calc {
          q;
          == (q / k) * k + q % k;
          == t * k + 0;
          == t * k;
          == k * t;
        }
      }

      calc {
        m;
        == d * q;
        == d * (k * t);
        == k * (d * t);
      }
      assert m % k == 0;
      assert m % k != 0; // since 2 <= k < d, from NoDivisorsLessThan(m,d)
    }
  }
}

lemma {:isolate_assertions} SmallestDivisorIsPrime(m: nat, d: nat)
  requires m > 1
  requires d >= 2
  requires m % d == 0
  requires NoDivisorsLessThan(m, d)
  ensures IsPrime(d)
{
  assert d >= 2;

  // Prove: forall k :: 2 <= k < d ==> d % k != 0
  forall k | 2 <= k < d
    ensures d % k != 0
  {
    if d % k == 0 {
      DividesTransitiveNat(m, d, k);
      assert m % k == 0;
      assert m % k != 0; // since 2 <= k < d, from NoDivisorsLessThan(m,d)
    }
  }
}

lemma {:isolate_assertions} MinimalDivisorQuotientAtLeastDiv(m: nat, d: nat)
  requires m > 1
  requires d >= 2
  requires m % d == 0
  requires NoDivisorsLessThan(m, d)
  ensures m == d ==> m / d == 1
  ensures m != d ==> m / d >= d
{
  if m == d {
    assert m / d == 1;
  } else {
    var q := m / d;
    assert m == d * q;

    assert q > 0;
    assert q != 1 by {
      if q == 1 {
        assert m == d * 1;
        assert m == d;
      }
    }
    assert q >= 2;

    if q < d {
      // Then q is a divisor of m with 2 <= q < d, contradicting NoDivisorsLessThan(m,d)
      assert m % q == 0 by {
        // m = d*q implies m is a multiple of q
        assert m == q * d;
        assert m % q == 0;
      }
      assert m % q != 0; // since 2 <= q < d, from NoDivisorsLessThan(m,d)
    }

    assert q >= d;
  }
}

method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures Product(f) == n
  ensures Nondecreasing(f)
  ensures forall i :: 0 <= i < |f| ==> IsPrime(f[i])
  ensures f == PFLoop(n, 2)
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1
      invariant rem >= 1
      invariant 2 <= div
      invariant Product(f) * rem == n
      invariant Nondecreasing(f)
      invariant forall i :: 0 <= i < |f| ==> IsPrime(f[i])
      invariant forall i :: 0 <= i < |f| ==> f[i] <= div
      invariant NoDivisorsLessThan(rem, div)
      invariant rem > 1 ==> div <= rem
      invariant f + PFLoop(rem, div) == PFLoop(n, 2)
      decreases rem, if rem > 1 && div <= rem then rem - div else 0
    {
        if rem % div == 0 {
            ghost var f0 := f;
            ghost var rem0 := rem;

            SmallestDivisorIsPrime(rem, div);

            if |f| > 0 {
              assert f[|f|-1] <= div;
            }

            assert rem != 1;
            assert div <= rem;
            assert PFLoop(rem, div) == [div] + PFLoop(rem / div, div);

            f := f + [div];

            NoDivisorsLessThan_Divide(rem0, div);
            MinimalDivisorQuotientAtLeastDiv(rem0, div);

            rem := rem / div;

            // helper for the calc step (parser-friendly)
            assert (f0 + [div]) + PFLoop(rem0 / div, div) == f0 + ([div] + PFLoop(rem0 / div, div)) by {
              SeqConcatAssoc(f0, [div], PFLoop(rem0 / div, div));
            }

            calc {
              f + PFLoop(rem, div);
              == (f0 + [div]) + PFLoop(rem0 / div, div);
              == f0 + ([div] + PFLoop(rem0 / div, div));
              == f0 + PFLoop(rem0, div);
              == PFLoop(n, 2);
            }
        }
        else {
            if rem > 1 {
              assert div <= rem;
              if div == rem {
                assert rem % div == 0;
              }
              assert div < rem;
              assert div + 1 <= rem;
            }

            NoDivisorsLessThan_Step(rem, div);

            assert rem != 1;
            assert div <= rem;
            assert PFLoop(rem, div) == PFLoop(rem, div + 1);
            assert PFLoop(rem, div + 1) == PFLoop(rem, div);

            calc {
              f + PFLoop(rem, div + 1);
              == f + PFLoop(rem, div);
              == PFLoop(n, 2);
            }

            div := div + 1;
        }
    }

    assert rem == 1;
    assert PFLoop(rem, div) == [];
    assert f + PFLoop(rem, div) == f;

    assert f == PFLoop(n, 2);
}

// A small computation lemma to help the concrete test
lemma {:isolate_assertions} PFLoop12Is223()
  ensures PFLoop(12, 2) == [2, 2, 3]
{
  assert PFLoop(12,2) == [2] + PFLoop(6,2);      // 12%2==0
  assert PFLoop(6,2)  == [2] + PFLoop(3,2);      // 6%2==0
  assert PFLoop(3,2)  == PFLoop(3,3);            // 3%2!=0
  assert PFLoop(3,3)  == [3] + PFLoop(1,3);      // 3%3==0
  assert PFLoop(1,3)  == [];                     // base
  calc {
    PFLoop(12,2);
    == [2] + PFLoop(6,2);
    == [2] + ([2] + PFLoop(3,2));
    == [2,2] + PFLoop(3,2);
    == [2,2] + PFLoop(3,3);
    == [2,2] + ([3] + PFLoop(1,3));
    == [2,2] + [3];
    == [2,2,3];
  }
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);
    assert f1 == PFLoop(12, 2);
    PFLoop12Is223();
    assert PFLoop(12, 2) == [2, 2, 3];
    assert f1 == [2, 2, 3];
}
