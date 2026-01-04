// Defining a function for real exponentiation
function pow(x: real, n: nat): real
  requires n >= 0
{
  if n == 0 then 1.0 else x * pow(x, n-1)
}

// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.
method FastExponentiation(x: real, n: nat) returns (p: real)
  ensures p == pow(x, n)
{
  p := 1.0; // partial result
  var mx: real := x; // remaining base (x)
  var mn: nat := n; // remaining exponent (n)
  while mn > 0 
    invariant p * pow(mx, mn) == pow(x, n) && mn >= 0 && p >= 0
  {
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
  assert p1 == pow(2.0, 8);
  var p2 := FastExponentiation(2.0, 0); 
  assert p2 == pow(2.0, 0);
  var p3 := FastExponentiation(-2.0, 1); 
  assert p3 == pow(-2.0, 1);
}
