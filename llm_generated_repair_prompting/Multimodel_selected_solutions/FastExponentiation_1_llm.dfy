// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.

ghost function Pow(x: real, n: nat): real
{
  if n == 0 then 1.0
  else x * Pow(x, n - 1)
}

lemma PowMultiply(x: real, a: nat, b: nat)
  ensures Pow(x, a + b) == Pow(x, a) * Pow(x, b)
{
  if a == 0 {
  } else {
    PowMultiply(x, a - 1, b);
  }
}

lemma PowSquare(x: real, n: nat)
  ensures Pow(x * x, n) == Pow(x, 2 * n)
{
  if n == 0 {
  } else {
    PowSquare(x, n - 1);
    calc {
      Pow(x * x, n);
      == (x * x) * Pow(x * x, n - 1);
      == (x * x) * Pow(x, 2 * (n - 1));
      == (x * x) * Pow(x, 2 * n - 2);
    }
    calc {
      Pow(x, 2 * n);
      == x * Pow(x, 2 * n - 1);
      == x * x * Pow(x, 2 * n - 2);
    }
  }
}

lemma PowDecompose(x: real, n: nat)
  requires n > 0
  ensures n % 2 == 1 ==> Pow(x, n) == x * Pow(x * x, n / 2)
  ensures n % 2 == 0 ==> Pow(x, n) == Pow(x * x, n / 2)
{
  PowSquare(x, n / 2);
  if n % 2 == 1 {
    assert n == 2 * (n / 2) + 1;
    PowMultiply(x, 1, 2 * (n / 2));
  } else {
    assert n == 2 * (n / 2);
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
  {
     PowDecompose(mx, mn);
     if mn % 2 == 1 { 
        p := p * mx; 
     } 
      mx := mx * mx;
      mn := mn / 2;
  }
}



// Test cases checked statically by Dafny!
method TestFastExponentiation() {
  var p1 := FastExponentiation(2.0, 8); 
  assert Pow(2.0, 8) == 256.0;
  assert p1 == 256.0;
  var p2 := FastExponentiation(2.0, 0); 
  assert p2 == 1.0;
  var p3 := FastExponentiation(-2.0, 1); 
  assert p3 == -2.0;
}
