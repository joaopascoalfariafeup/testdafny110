// Computes the quotient 'q' and remainder 'r' of  the integer division
// of a (non-negative) dividend 'n' by a (positive) divisor 'd'.
method Div(n: nat, d: nat) returns (q: nat, r: nat)
  requires d > 0
  ensures n == q * d + r
  ensures r < d
{
  q := 0; 
  r := n;  
  while r >= d
    invariant n == q * d + r
    decreases r
  {
    q := q + 1;
    r := r - d;
  }
}

// A simple test case (checked statically by Dafny)!
method TestDiv() 
{
    var q, r := Div(15, 6);
    assert q == 2 && r == 3;
}
