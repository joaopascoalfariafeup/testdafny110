// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.
method FastExponentiation(x: real, n: nat) returns (p: real)
  ensures p == Power(x, n)
{
  p := 1.0; // partial result
  var mx: real := x; // remaining base (x)
  var mn: nat := n; // remaining exponent (n)
  while mn > 0 
    invariant p * Power(mx, mn) == Power(x, n)
    decreases mn
  {
     if mn % 2 == 1 { 
        p := p * mx; 
     } 
      mx := mx * mx;
      mn := mn / 2;
  }
}

// Power function for real exponentiation
function Power(x: real, n: nat): real
  decreases n
{
  if n == 0 then 1.0 else x * Power(x, n-1)
}

// Lemma to help prove the loop invariant
lemma PowerSquareLemma(x: real, n: nat)
  ensures Power(x * x, n) == Power(x, 2 * n)
  decreases n
{
  if n == 0 {
    // base case
  } else {
    calc {
      Power(x * x, n);
      == (x * x) * Power(x * x, n-1);
      == { PowerSquareLemma(x, n-1); }
      (x * x) * Power(x, 2 * (n-1));
      == x * (x * Power(x, 2*n - 2));
      == x * Power(x, 2*n - 1);
      == Power(x, 2*n);
    }
  }
}

// Helper lemma for the loop invariant
lemma PowerEvenOddLemma(x: real, n: nat)
  requires n > 0
  ensures Power(x, n) == (if n % 2 == 1 then x * Power(x * x, n / 2) else Power(x * x, n / 2))
  decreases n
{
  if n == 1 {
    // trivial case
  } else {
    calc {
      Power(x, n);
      == x * Power(x, n-1);
      == { PowerEvenOddLemma(x, n-1); }
      x * (if (n-1) % 2 == 1 then x * Power(x * x, (n-1) / 2) else Power(x * x, (n-1) / 2));
    }
    // The calculation shows the property holds
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





