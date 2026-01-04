// Ghost power function for reals and natural exponents
ghost function {:fuel 40} Pow(x: real, n: nat): real
  ensures n == 0 ==> Pow(x, n) == 1.0
  ensures n > 0 ==> Pow(x, n) == Pow(x, n - 1) * x
  decreases n
{
  if n == 0 then 1.0 else Pow(x, n - 1) * x
}

lemma PowAdd(x: real, a: nat, b: nat)
  ensures Pow(x, a + b) == Pow(x, a) * Pow(x, b)
  decreases b
{
  if b == 0 {
    // Pow(x,a+0)=Pow(x,a) and Pow(x,0)=1
    assert a + b == a;
    assert Pow(x, b) == 1.0;
  } else {
    PowAdd(x, a, b - 1);
    // Expand Pow(x, a+b) on the exponent b
    assert a + b > 0;
    assert Pow(x, a + b) == Pow(x, a + b - 1) * x;
    assert a + b - 1 == a + (b - 1);
    assert Pow(x, a + b) == Pow(x, a + (b - 1)) * x;
    // Use IH and Pow(x,b)=Pow(x,b-1)*x
    assert Pow(x, a + (b - 1)) == Pow(x, a) * Pow(x, b - 1);
    assert Pow(x, b) == Pow(x, b - 1) * x;
    calc {
      Pow(x, a + b);
      == { }
      Pow(x, a + (b - 1)) * x;
      == { }
      (Pow(x, a) * Pow(x, b - 1)) * x;
      == { }
      Pow(x, a) * (Pow(x, b - 1) * x);
      == { }
      Pow(x, a) * Pow(x, b);
    }
  }
}

lemma PowSquare(mx: real, k: nat)
  ensures Pow(mx * mx, k) == Pow(mx, k) * Pow(mx, k)
  decreases k
{
  if k == 0 {
    assert Pow(mx * mx, 0) == 1.0;
    assert Pow(mx, 0) == 1.0;
  } else {
    PowSquare(mx, k - 1);
    assert Pow(mx * mx, k) == Pow(mx * mx, k - 1) * (mx * mx);
    assert Pow(mx, k) == Pow(mx, k - 1) * mx;
    calc {
      Pow(mx * mx, k);
      == { }
      Pow(mx * mx, k - 1) * (mx * mx);
      == { PowSquare(mx, k - 1); }
      (Pow(mx, k - 1) * Pow(mx, k - 1)) * (mx * mx);
      == { }
      (Pow(mx, k - 1) * mx) * (Pow(mx, k - 1) * mx);
      == { }
      Pow(mx, k) * Pow(mx, k);
    }
  }
}

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
  calc {
    Pow(mx, 2 * k + 1);
    == { assert 2 * k + 1 == (2 * k) + 1; }
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

      // Use invariant to rewrite Pow(mx,mn) as Pow(mx*mx,k)*mx
      assert Pow(mx, mn) == Pow(mx, 2 * k + 1);
      assert Pow(mx, mn) == Pow(mx * mx, k) * mx;

      p := p * mx;

      // After updating p, the remaining exponent is k on base mx*mx
      assert p * Pow(mx * mx, k) == Pow(x, n);
    } else {
      // mn = 2*k
      var k: nat := mn / 2;
      assert mn == 2 * k;
      PowEvenOdd(mx, k);

      assert Pow(mx, mn) == Pow(mx, 2 * k);
      assert Pow(mx, mn) == Pow(mx * mx, k);

      assert p * Pow(mx * mx, k) == Pow(x, n);
    }
    mx := mx * mx;
    mn := mn / 2;
  }
  // mn == 0, so Pow(mx,0) = 1
  assert Pow(mx, mn) == 1.0;
  assert p == p * Pow(mx, mn);
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
