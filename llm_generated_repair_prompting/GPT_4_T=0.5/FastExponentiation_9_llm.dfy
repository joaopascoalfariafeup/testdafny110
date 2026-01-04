
function pow(x: real, n: nat): real
  requires n >= 0
{
  if n == 0 then 1.0 else x * pow(x, n-1)
}

method FastExponentiation(x: real, n: nat) returns (p: real)
  ensures p == pow(x, n)
{
  p := 1.0; 
  var mx: real := x;
  var mn: nat := n;
  while mn > 0 
    invariant p * pow(mx, 2*mn) == pow(x, n) && 0 <= mn <= n && p >= 0.0
  {
     if mn % 2 == 1 { 
        p := p * mx; 
     } 
      mx := mx * mx;
      mn := mn / 2;
  }
}

method TestFastExponentiation() {
  var p1 := FastExponentiation(2.0, 8); 
  assert p1 == pow(2.0, 8);
  var p2 := FastExponentiation(2.0, 0); 
  assert p2 == pow(2.0, 0);
  var p3 := FastExponentiation(-2.0, 1); 
  assert p3 == pow(-2.0, 1);
}


