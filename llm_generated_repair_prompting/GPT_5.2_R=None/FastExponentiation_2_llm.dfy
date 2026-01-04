// Ghost power function for reals and natural exponents
ghost function {:fuel 20} Pow(x: real, n: nat): real
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
  } else {
    PowAdd(x, a, b - 1);
    // Pow(x, a+b) = Pow(x, a+(b-1)) * x
    //            = (Pow(x,a)*Pow(x,b-1))*x
    //            = Pow(x,a)*Pow(x,b)
  }
}

lemma PowEvenOdd(mx: real, k: nat)
  ensures Pow(mx, 2 * k) == Pow(mx * mx, k)
  ensures Pow(mx, 2 * k + 1) == Pow(mx * mx, k) * mx
{
  // Even case
  calc {
    Pow(mx, 2 * k);
    == { PowAdd(mx, k, k); }
    Pow(mx, k) * Pow(mx, k);
  }
  // Relate Pow(mx*mx,k) to Pow(mx,k)*Pow(mx,k)
  // Prove by simple induction on k inside a calc:
  var i: nat := 0;
  var lhs: real := 1.0;
  var rhs: real := 1.0;
  while i < k
    invariant i <= k
    invariant lhs == Pow(mx * mx, i)
    invariant rhs == Pow(mx, i) * Pow(mx, i)
    decreases k - i
  {
    lhs := lhs * (mx * mx);
    rhs := (Pow(mx, i) * mx) * (Pow(mx, i) * mx);
    i := i + 1;
    // Help Dafny rewrite the Pow terms
    assert Pow(mx * mx, i) == Pow(mx * mx, i - 1) * (mx * mx);
    assert Pow(mx, i) == Pow(mx, i - 1) * mx;
    assert rhs == Pow(mx, i) * Pow(mx, i);
    assert lhs == Pow(mx * mx, i);
  }
  assert Pow(mx * mx, k) == Pow(mx, k) * Pow(mx, k);

  // Odd case
  calc {
    Pow(mx, 2 * k + 1);
    == { assert 2 * k + 1 == 2 * k + 0 + 1; }
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
      // p' * Pow(mx*mx, k) = p*mx * Pow(mx*mx,k) = p*Pow(mx,mn)
      p := p * mx;
      assert p * Pow(mx * mx, k) == Pow(x, n);
    } else {
      // mn = 2*k
      var k: nat := mn / 2;
      assert mn == 2 * k;
      PowEvenOdd(mx, k);
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
