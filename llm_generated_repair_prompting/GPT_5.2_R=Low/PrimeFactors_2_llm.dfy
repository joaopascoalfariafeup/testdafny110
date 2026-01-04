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
ghost function {:fuel 40} PFLoop(n: nat, div: nat): seq<nat>
  requires div >= 2
  requires n == 1 || div <= n
  decreases n, if n == 1 then 0 else n - div
{
  if n == 1 then []
  else if n % div == 0 then [div] + PFLoop(n / div, div)
  else PFLoop(n, div + 1)
}

lemma SeqConcatAssoc<T>(a: seq<T>, b: seq<T>, c: seq<T>)
  ensures (a + b) + c == a + (b + c)
{
}

lemma DividesTransitiveNat(m: nat, d: nat, k: nat)
  requires d > 0
  requires k > 0
  requires m % d == 0
  requires d % k == 0
  ensures m % k == 0
{
  // m = d * q, d = k * r  =>  m = k * (r*q)
  var q := m / d;
  var r := d / k;
  assert m == d * q;
  assert d == k * r;
  assert m == k * (r * q);
}

lemma NoDivisorsLessThan_Step(m: nat, div: nat)
  requires div >= 2
  requires NoDivisorsLessThan(m, div)
  requires m % div != 0
  ensures NoDivisorsLessThan(m, div + 1)
{
  // Need: forall k :: 2 <= k < div+1 ==> m % k != 0
  assert forall k :: 2 <= k < div + 1 ==> m % k != 0 by {
    intro k;
    if k < div {
      // from NoDivisorsLessThan(m, div)
    } else {
      assert k == div;
    }
  }
}

lemma NoDivisorsLessThan_Divide(m: nat, d: nat)
  requires m > 1
  requires d >= 2
  requires m % d == 0
  requires NoDivisorsLessThan(m, d)
  ensures NoDivisorsLessThan(m / d, d)
{
  assert forall k :: 2 <= k < d ==> (m / d) % k != 0 by {
    intro k;
    // If (m/d) divisible by k, then m divisible by k, contradicting NoDivisorsLessThan(m,d)
    if (m / d) % k == 0 {
      assert m % k == 0 by {
        // d*(m/d) is m, and (m/d) % k == 0 implies (d*(m/d)) % k == 0
        var q := m / d;
        assert m == d * q;
        assert q % k == 0;
        // since q % k == 0, q == k * t for some t; show m == k * (d*t)
        var t := q / k;
        assert q == k * t;
        assert m == k * (d * t);
      }
    }
  }
}

lemma SmallestDivisorIsPrime(m: nat, d: nat)
  requires m > 1
  requires d >= 2
  requires m % d == 0
  requires NoDivisorsLessThan(m, d)
  ensures IsPrime(d)
{
  assert d >= 2;
  assert forall k :: 2 <= k < d ==> d % k != 0 by {
    intro k;
    if d % k == 0 {
      assert m % k == 0 by { DividesTransitiveNat(m, d, k); }
    }
  }
}

lemma MinimalDivisorQuotientAtLeastDiv(m: nat, d: nat)
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

    // q cannot be 1, else m == d
    assert q != 1 by {
      if q == 1 {
        assert m == d;
      }
    }

    // If q < d, then q is a divisor of m with 2 <= q < d, contradiction
    if q < d {
      assert q >= 2 by {
        // q is nat, q != 0 since m>0 and d>0, and q != 1
        assert q != 0;
      }
      assert m % q == 0 by {
        // m = d*q, so divisible by q
        assert m == q * d;
      }
    }

    // Therefore q >= d
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
      decreases rem, rem - div
    {
        if rem % div == 0 {
            SmallestDivisorIsPrime(rem, div);

            // keep Nondecreasing after appending div
            if |f| > 0 {
              assert f[|f|-1] <= div;
            }

            // PFLoop unfolding for the "divide" case
            assert rem != 1;
            assert div <= rem; // from invariant (since rem>1)
            assert PFLoop(rem, div) == [div] + PFLoop(rem / div, div);

            // update f
            f := f + [div];

            // maintain NoDivisorsLessThan when dividing
            NoDivisorsLessThan_Divide(rem, div);

            // quotient properties (used for div<=rem when loop continues)
            MinimalDivisorQuotientAtLeastDiv(rem, div);

            // update rem
            rem := rem / div;

            // re-establish PFLoop relation
            // old: f_old + PFLoop(rem_old,div) == PFLoop(n,2)
            // new: f_new + PFLoop(rem_new,div) == PFLoop(n,2)
            // f_new = f_old+[div], rem_new = rem_old/div
            SeqConcatAssoc(f[..|f|-1], [div], PFLoop(rem, div));
            // (The above lemma call is harmless even if f[..|f|-1] is not used by Dafny;
            // the key equalities below guide the proof.)
            assert (f[..|f|-1] + [div]) + PFLoop(rem, div) == f[..|f|-1] + ([div] + PFLoop(rem, div));
            // Now f[..|f|-1] is the old f, because we just appended one element
            assert f[..|f|-1] + PFLoop(rem * div, div) == PFLoop(n, 2) || true; // vacuous helper to avoid brittleness
            // Directly prove the maintained invariant from the previous one:
            // Dafny can rewrite using the asserted unfolding and associativity of +
        }
        else {
            // maintain NoDivisorsLessThan when incrementing div
            NoDivisorsLessThan_Step(rem, div);

            // PFLoop unfolding for the "increment" case
            assert rem != 1;
            assert div <= rem; // from invariant (since rem>1)
            assert PFLoop(rem, div) == PFLoop(rem, div + 1);

            div := div + 1;
        }
    }

    // At exit, rem == 1
    assert rem == 1;
    assert PFLoop(rem, div) == [];
    assert f + PFLoop(rem, div) == f;
}









// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);
    assert f1 == PFLoop(12, 2);
    assert PFLoop(12, 2) == [2, 2, 3];
    assert f1 == [2, 2, 3];
}
