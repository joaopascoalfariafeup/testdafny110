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

     if oldmn % 2 == 1 {
       assert Pow(oldmx, oldmn) == oldmx * Pow(oldmx * oldmx, oldmn / 2);
       assert p * Pow(mx, mn) == (oldp * oldmx) * Pow(oldmx * oldmx, oldmn / 2);
       assert p * Pow(mx, mn) == oldp * Pow(oldmx, oldmn);
     } else {
       assert Pow(oldmx, oldmn) == Pow(oldmx * oldmx, oldmn / 2);
       assert p * Pow(mx, mn) == oldp * Pow(oldmx * oldmx, oldmn / 2);
       assert p * Pow(mx, mn) == oldp * Pow(oldmx, oldmn);
     }
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
