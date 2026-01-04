// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.

function Pow(x: real, n: nat): real
  decreases n
{
  if n == 0 then 1.0 else Pow(x, n - 1) * x
}

lemma PowSquare(x: real, k: nat)
  ensures Pow(x, 2 * k) == Pow(x * x, k)
  decreases k
{
  if k == 0 {
  } else {
    PowSquare(x, k - 1);
    assert 2 * k == 2 * (k - 1) + 2;
    assert Pow(x, 2 * k) == Pow(x, 2 * (k - 1) + 2);
    assert Pow(x, 2 * (k - 1) + 2) == Pow(x, 2 * (k - 1) + 1) * x;
    assert Pow(x, 2 * (k - 1) + 1) == Pow(x, 2 * (k - 1)) * x;
    assert Pow(x, 2 * k) == (Pow(x, 2 * (k - 1)) * x) * x;
    assert Pow(x, 2 * k) == Pow(x, 2 * (k - 1)) * (x * x);
    assert Pow(x, 2 * (k - 1)) == Pow(x * x, k - 1);
    assert Pow(x * x, k) == Pow(x * x, k - 1) * (x * x);
  }
}

lemma PowDecompose(x: real, m: nat)
  ensures Pow(x, m) == if m % 2 == 0 then Pow(x * x, m / 2) else Pow(x * x, m / 2) * x
{
  var k := m / 2;
  if m % 2 == 0 {
    assert m == 2 * k;
    PowSquare(x, k);
  } else {
    assert m == 2 * k + 1;
    PowSquare(x, k);
    assert Pow(x, m) == Pow(x, 2 * k + 1);
    assert Pow(x, 2 * k + 1) == Pow(x, 2 * k) * x;
  }
}

method FastExponentiation(x: real, n: nat) returns (p: real)
  ensures p == Pow(x, n)
{
  p := 1.0; // partial result
  var mx: real := x; // remaining base (x)
  var mn: nat := n; // remaining exponent (n)
  while mn > 0 
    invariant p * Pow(mx, mn) == Pow(x, n)
    decreases mn
  {
     var oldp := p;
     var oldmx := mx;
     var oldmn := mn;

     if mn % 2 == 1 { 
        p := p * mx; 
     } 
      mx := mx * mx;
      mn := mn / 2;

      PowDecompose(oldmx, oldmn);
      if oldmn % 2 == 0 {
        assert oldmn / 2 == mn;
        assert oldmx * oldmx == mx;
        assert Pow(oldmx, oldmn) == Pow(mx, mn);
        assert oldp * Pow(oldmx, oldmn) == p * Pow(mx, mn);
      } else {
        assert oldmn / 2 == mn;
        assert oldmx * oldmx == mx;
        assert Pow(oldmx, oldmn) == Pow(mx, mn) * oldmx;
        assert oldp * Pow(oldmx, oldmn) == oldp * (Pow(mx, mn) * oldmx);
        assert oldp * (Pow(mx, mn) * oldmx) == (oldp * oldmx) * Pow(mx, mn);
        assert p == oldp * oldmx;
        assert oldp * Pow(oldmx, oldmn) == p * Pow(mx, mn);
      }
      assert p * Pow(mx, mn) == Pow(x, n);
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
