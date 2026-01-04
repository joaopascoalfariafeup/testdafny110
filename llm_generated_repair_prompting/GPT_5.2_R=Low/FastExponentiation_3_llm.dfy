// Computes x^n in time O(log n) and space O(1)
// using the fast exponentiation algorithm.

function Pow(x: real, n: nat): real
  decreases n
{
  if n == 0 then 1.0 else x * Pow(x, n - 1)
}

lemma PowSucc(x: real, n: nat)
  ensures Pow(x, n + 1) == x * Pow(x, n)
{
  assert n + 1 > 0;
  calc {
    Pow(x, n + 1);
    == { }
    x * Pow(x, (n + 1) - 1);
    == { assert (n + 1) - 1 == n; }
    x * Pow(x, n);
  }
}

lemma PowTwoMore(x: real, n: nat)
  ensures Pow(x, n + 2) == (x * x) * Pow(x, n)
{
  PowSucc(x, n + 1);
  PowSucc(x, n);
  calc {
    Pow(x, n + 2);
    == { assert n + 2 == (n + 1) + 1; PowSucc(x, n + 1); }
    x * Pow(x, n + 1);
    == { PowSucc(x, n); }
    x * (x * Pow(x, n));
    == { }
    (x * x) * Pow(x, n);
  }
}

lemma PowEven(x: real, k: nat)
  ensures Pow(x, 2 * k) == Pow(x * x, k)
  decreases k
{
  if k == 0 {
    // Pow(x,0) == 1 == Pow(x*x,0)
  } else {
    PowEven(x, k - 1);

    assert k > 0;
    assert 2 * k == 2 * (k - 1) + 2;

    PowTwoMore(x, 2 * (k - 1));
    PowSucc(x * x, k - 1); // Pow(x*x, (k-1)+1) == (x*x)*Pow(x*x,k-1)

    calc {
      Pow(x, 2 * k);
      == { assert 2 * k == 2 * (k - 1) + 2; }
      Pow(x, 2 * (k - 1) + 2);
      == { PowTwoMore(x, 2 * (k - 1)); }
      (x * x) * Pow(x, 2 * (k - 1));
      == { PowEven(x, k - 1); }
      (x * x) * Pow(x * x, k - 1);
      == { assert Pow(x * x, k) == (x * x) * Pow(x * x, k - 1); }
      Pow(x * x, k);
    }
  }
}

lemma PowOdd(x: real, k: nat)
  ensures Pow(x, 2 * k + 1) == x * Pow(x * x, k)
{
  PowEven(x, k);
  assert 2 * k + 1 > 0;
  calc {
    Pow(x, 2 * k + 1);
    == { }
    x * Pow(x, (2 * k + 1) - 1);
    == { assert (2 * k + 1) - 1 == 2 * k; }
    x * Pow(x, 2 * k);
    == { PowEven(x, k); }
    x * Pow(x * x, k);
  }
}

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
        var k: nat := mn / 2;
        assert mn == 2 * k + 1;
        PowOdd(mx, k);

        var p0 := p;
        p := p * mx;

        // From PowOdd: Pow(mx,mn) = mx * Pow(mx*mx,k)
        // Need: (p0*mx)*Pow(mx*mx,k) == p0*Pow(mx,mn)
        calc {
          p * Pow(mx * mx, k);
          == { }
          (p0 * mx) * Pow(mx * mx, k);
          == { }
          p0 * (mx * Pow(mx * mx, k));
          == { assert Pow(mx, mn) == mx * Pow(mx * mx, k); }
          p0 * Pow(mx, mn);
        }
     } else {
        var k: nat := mn / 2;
        assert mn == 2 * k;
        PowEven(mx, k);
        assert Pow(mx, mn) == Pow(mx * mx, k);
        assert p * Pow(mx * mx, k) == p * Pow(mx, mn);
     }
      mx := mx * mx;
      mn := mn / 2;
  }
  assert mn == 0;
  assert Pow(mx, mn) == 1.0;
  assert p == Pow(x, n);
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

