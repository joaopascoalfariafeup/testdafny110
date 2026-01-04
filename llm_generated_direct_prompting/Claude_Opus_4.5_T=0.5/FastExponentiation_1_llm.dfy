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

lemma FastExpLemma(p: real, mx: real, mn: nat)
  ensures mn % 2 == 1 ==> p * mx * Pow(mx * mx, mn / 2) == p * Pow(mx, mn)
  ensures mn % 2 == 0 ==> p * Pow(mx * mx, mn / 2) == p * Pow(mx, mn)
{
  PowSquare(mx, mn / 2);
  if mn % 2 == 1 {
    calc {
      p * mx * Pow(mx * mx, mn / 2);
      == p * mx * Pow(mx, 2 * (mn / 2));
      == p * mx * Pow(mx, mn - 1);
    }
    PowMultiply(mx, 1, mn - 1);
  } else {
    calc {
      p * Pow(mx * mx, mn / 2);
      == p * Pow(mx, 2 * (mn / 2));
      == p * Pow(mx, mn);
    }
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
     FastExpLemma(p, mx, mn);
     if mn % 2 == 1 { 
        p := p * mx; 
     } 
      mx := mx * mx;
      mn := mn / 2;
  }
}



// Test cases checked statically by Dafny!
method {:fuel Pow, 9} TestFastExponentiation() {
  var p1 := FastExponentiation(2.0, 8); 
  assert p1 == 256.0;
  var p2 := FastExponentiation(2.0, 0); 
  assert p2 == 1.0;
  var p3 := FastExponentiation(-2.0, 1); 
  assert p3 == -2.0;
}
