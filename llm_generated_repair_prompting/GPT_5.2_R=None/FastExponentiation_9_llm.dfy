// Ghost power function for reals and natural exponents
ghost function {:fuel 40} Pow(x: real, n: nat): real
  decreases n
{
  if n == 0 then 1.0 else Pow(x, n - 1) * x
}

// Convenience lemma: unfold Pow at a positive exponent
lemma PowUnfold(x: real, n: nat)
  requires n > 0
  ensures Pow(x, n) == Pow(x, n - 1) * x
{
}

// Also useful: Pow at 0
lemma Pow0(x: real)
  ensures Pow(x, 0) == 1.0
{
}

// Associativity/commutativity for real multiplication (needed explicitly)
lemma MulAssoc(a: real, b: real, c: real)
  ensures (a * b) * c == a * (b * c)
{
}
lemma MulComm(a: real, b: real)
  ensures a * b == b * a
{
}

// Basic identities (sometimes useful for calc)
lemma MulIdRight(a: real)
  ensures a * 1.0 == a
{
}
lemma MulIdLeft(a: real)
  ensures 1.0 * a == a
{
}

// Exponent law: x^(a+b) = x^a * x^b
lemma PowAdd(x: real, a: nat, b: nat)
  ensures Pow(x, a + b) == Pow(x, a) * Pow(x, b)
  decreases b
{
  if b == 0 {
    calc {
      Pow(x, a + b);
      == { }
      Pow(x, a);
      == { Pow0(x); }
      Pow(x, a) * Pow(x, b);
    }
  } else {
    PowAdd(x, a, b - 1);

    PowUnfold(x, a + b);
    PowUnfold(x, b);
    assert a + b - 1 == a + (b - 1);

    calc {
      Pow(x, a + b);
      == { }
      Pow(x, a + b - 1) * x;
      == { assert a + b - 1 == a + (b - 1); }
      Pow(x, a + (b - 1)) * x;
      == { PowAdd(x, a, b - 1); }
      (Pow(x, a) * Pow(x, b - 1)) * x;
      == { MulAssoc(Pow(x, a), Pow(x, b - 1), x); }
      Pow(x, a) * (Pow(x, b - 1) * x);
      == { PowUnfold(x, b); }
      Pow(x, a) * Pow(x, b);
    }
  }
}

// Square law: (mx*mx)^k = mx^k * mx^k
lemma PowSquare(mx: real, k: nat)
  ensures Pow(mx * mx, k) == Pow(mx, k) * Pow(mx, k)
  decreases k
{
  if k == 0 {
    calc {
      Pow(mx * mx, k);
      == { }
      Pow(mx * mx, 0);
      == { }
      1.0;
      == { Pow0(mx); }
      Pow(mx, 0) * Pow(mx, 0);
      == { }
      Pow(mx, k) * Pow(mx, k);
    }
  } else {
    PowSquare(mx, k - 1);

    PowUnfold(mx * mx, k);
    PowUnfold(mx, k);

    // After unfolding:
    // Pow(mx*mx,k) = Pow(mx*mx,k-1) * (mx*mx)
    // and by IH Pow(mx*mx,k-1) = Pow(mx,k-1)*Pow(mx,k-1)
    calc {
      Pow(mx * mx, k);
      == { }
      Pow(mx * mx, k - 1) * (mx * mx);
      == { PowSquare(mx, k - 1); }
      (Pow(mx, k - 1) * Pow(mx, k - 1)) * (mx * mx);
      == { MulAssoc(Pow(mx, k - 1) * Pow(mx, k - 1), mx, mx); }
      ((Pow(mx, k - 1) * Pow(mx, k - 1)) * mx) * mx;
      == { MulAssoc(Pow(mx, k - 1), Pow(mx, k - 1), mx); }
      (Pow(mx, k - 1) * (Pow(mx, k - 1) * mx)) * mx;
      == { MulAssoc(Pow(mx, k - 1), (Pow(mx, k - 1) * mx), mx); }
      Pow(mx, k - 1) * ((Pow(mx, k - 1) * mx) * mx);
      == { MulAssoc(Pow(mx, k - 1), Pow(mx, k - 1) * mx, mx); }
      Pow(mx, k - 1) * (Pow(mx, k - 1) * (mx * mx));
      == { MulAssoc(Pow(mx, k - 1), Pow(mx, k - 1), mx * mx); }
      (Pow(mx, k - 1) * Pow(mx, k - 1)) * (mx * mx);
      == { PowUnfold(mx, k); }
      Pow(mx, k - 1) * Pow(mx, k);
      == { MulComm(Pow(mx, k - 1), Pow(mx, k)); }
      Pow(mx, k) * Pow(mx, k - 1);
      == { PowUnfold(mx, k); }
      Pow(mx, k) * Pow(mx, k);
    }
  }
}

// Even/odd decomposition
lemma PowEvenOdd(mx: real, k: nat)
  ensures Pow(mx, 2 * k) == Pow(mx * mx, k)
  ensures Pow(mx, 2 * k + 1) == Pow(mx * mx, k) * mx
{
  PowAdd(mx, k, k);
  PowSquare(mx, k);

  // Even case
  calc {
    Pow(mx, 2 * k);
    == { assert 2 * k == k + k; }
    Pow(mx, k + k);
    == { PowAdd(mx, k, k); }
    Pow(mx, k) * Pow(mx, k);
    == { PowSquare(mx, k); }
    Pow(mx * mx, k);
  }

  // Odd case
  PowUnfold(mx, 2 * k + 1);

  calc {
    Pow(mx, 2 * k + 1);
    == { }
    Pow(mx, 2 * k) * mx;
    == { assert Pow(mx, 2 * k) == Pow(mx * mx, k); }
    Pow(mx * mx, k) * mx;
  }
}

// Computes x^n in time O(log n) and space O(1)
// using the fast exponentiation algorithm.
method FastExponentiation(x: real, n: nat) returns (p: real)
  ensures p == Pow(x, n)
{
  p := 1.0; // partial result
  var mx: real := x; // remaining base (x)
  var mn: nat := n; // remaining exponent (n)
  while mn > 0
    invariant mn <= n
    invariant p * Pow(mx, mn) == Pow(x, n)
    decreases mn
  {
    if mn % 2 == 1 {
      // mn = 2*k+1
      var k: nat := mn / 2;
      assert mn == 2 * k + 1;
      PowEvenOdd(mx, k);

      assert Pow(mx, mn) == Pow(mx, 2 * k + 1);
      assert Pow(mx, mn) == Pow(mx * mx, k) * mx;

      // rewrite invariant using the odd decomposition
      assert p * Pow(mx, mn) == Pow(x, n);
      assert p * Pow(mx, mn) == p * (Pow(mx * mx, k) * mx);

      // (p * (A * mx)) == (p * mx) * A
      calc {
        p * (Pow(mx * mx, k) * mx);
        == { MulAssoc(p, Pow(mx * mx, k), mx); }
        (p * Pow(mx * mx, k)) * mx;
        == { MulComm(p * Pow(mx * mx, k), mx); }
        mx * (p * Pow(mx * mx, k));
        == { MulAssoc(mx, p, Pow(mx * mx, k)); }
        (mx * p) * Pow(mx * mx, k);
        == { MulComm(mx, p); }
        (p * mx) * Pow(mx * mx, k);
      }

      p := p * mx;
      assert p * Pow(mx * mx, k) == Pow(x, n);
    } else {
      // mn = 2*k
      var k: nat := mn / 2;
      assert mn == 2 * k;
      PowEvenOdd(mx, k);

      assert Pow(mx, mn) == Pow(mx, 2 * k);
      assert Pow(mx, mn) == Pow(mx * mx, k);

      assert p * Pow(mx, mn) == Pow(x, n);
      assert p * Pow(mx, mn) == p * Pow(mx * mx, k);
      assert p * Pow(mx * mx, k) == Pow(x, n);
    }
    mx := mx * mx;
    mn := mn / 2;
  }
  Pow0(mx);
  assert Pow(mx, mn) == 1.0;
  assert p == p * Pow(mx, mn);
  // conclude from loop invariant at mn==0
  calc {
    p;
    == { assert Pow(mx, mn) == 1.0; }
    p * Pow(mx, mn);
    == { }
    Pow(x, n);
  }
}

// Test cases checked statically by Dafny!
method TestFastExponentiation() {
  var p1 := FastExponentiation(2.0, 8);
  assert p1 == 256.0;
  var p2 := FastExponentiation(2.0, 0);
  assert p2 == 1.0;
  var p3 := FastExponentiation(-2.0, 1);
  assert p3 == -2.0;
}
