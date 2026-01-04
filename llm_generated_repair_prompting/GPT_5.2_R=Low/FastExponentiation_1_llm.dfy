// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.

function Pow(x: real, n: nat): real
  decreases n
{
  if n == 0 then 1.0 else x * Pow(x, n - 1)
}

lemma PowEven(x: real, k: nat)
  ensures Pow(x, 2 * k) == Pow(x * x, k)
  decreases k
{
  if k == 0 {
  } else {
    PowEven(x, k - 1);
    calc {
      Pow(x, 2 * k);
      == { assert 2 * k == 2 * (k - 1) + 2; }
      Pow(x, 2 * (k - 1) + 2);
      == Pow(x, 2 * (k - 1) + 1) * x;
      == (Pow(x, 2 * (k - 1)) * x) * x;
      == Pow(x, 2 * (k - 1)) * (x * x);
      == { PowEven(x, k - 1); }
      Pow(x * x, k - 1) * (x * x);
      == Pow(x * x, k);
    }
  }
}

lemma PowOdd(x: real, k: nat)
  ensures Pow(x, 2 * k + 1) == x * Pow(x * x, k)
{
  PowEven(x, k);
  calc {
    Pow(x, 2 * k + 1);
    == Pow(x, 2 * k) * x;
    == { PowEven(x, k); }
    Pow(x * x, k) * x;
    == x * Pow(x * x, k);
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
        p := p * mx;
        assert p * Pow(mx * mx, k) == old(p) * Pow(mx, mn);
     } else {
        var k: nat := mn / 2;
        assert mn == 2 * k;
        PowEven(mx, k);
        assert p * Pow(mx * mx, k) == p * Pow(mx, mn);
     }
      mx := mx * mx;
      mn := mn / 2;
  }
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
