// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.
function Pow(x: real, n: nat): real
  decreases n
{
  if n == 0 then 1.0
  else if n % 2 == 0 then Pow(x * x, n / 2)
  else x * Pow(x * x, n / 2)
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
        assert Pow(mx, mn) == mx * Pow(mx * mx, mn / 2);
        p := p * mx;
        assert p * Pow(mx * mx, mn / 2) == Pow(x, n);
     } else {
        assert Pow(mx, mn) == Pow(mx * mx, mn / 2);
        assert p * Pow(mx * mx, mn / 2) == Pow(x, n);
     }
      mx := mx * mx;
      mn := mn / 2;
  }
  assert Pow(mx, 0) == 1.0;
  assert p == p * Pow(mx, 0);
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
