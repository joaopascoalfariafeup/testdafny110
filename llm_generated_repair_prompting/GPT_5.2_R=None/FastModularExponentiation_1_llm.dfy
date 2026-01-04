/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

function Pow(x: nat, n: nat): nat
{
  if n == 0 then 1 else x * Pow(x, n - 1)
}

function PowMod(x: nat, n: nat, m: nat): nat
  requires m > 0
{
  Pow(x, n) % m
}

// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.
method FastExponentiation(x: nat, n: nat) returns (p: nat)
  ensures p == Pow(x, n)
{
    var mx: nat  := x; // remaining base
    var mn: nat := n; // remaining exponent
    p := 1; // partial result
    while mn > 0 
      invariant p * Pow(mx, mn) == Pow(x, n)
      decreases mn
    {
        if mn % 2 == 1 {
            p := p * mx;
        } 
        mx := mx * mx;
        mn := mn / 2;
    }
}


// Iterative computation of x^n mod m in time O(log n), 
// by the fast modular exponentiation algorithm, avoiding overflows.
method FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
  ensures m == 1 ==> res == 0
  ensures m > 1 ==> res == PowMod(x, n, m)
{
    if m == 1 {
        return 0; // x^n % 1 == 0
    }

    var mn: nat := n; // remaining exponent


    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    while mn > 0 
      invariant m > 1
      invariant mx2 < m
      invariant p2 < m
      invariant (p2 * Pow(mx2, mn)) % m == PowMod(x, n, m)
      decreases mn
    {
        if mn % 2 == 1 {
            p2 := (p2 * mx2) % m;
        } 
        mn := mn / 2;
        mx2 := (mx2 * mx2) % m;
    }
    
    return p2;
}




// A few test cases (checked statically by Dafny).
method TestModularExponentiation() {
    var p1 := FastExponentiation(2, 10);
    assert p1 == 1024;

    var p2 := FastModularExponentiation(2, 10, 7);
    assert p2 == 2;

    var p3 := FastExponentiation(10, 6);
    assert p3 == 1000000;

    var p4 := FastModularExponentiation(10, 6, 9);
    assert p4 == 1;

    var p5 := FastModularExponentiation(1000, 1000, 1);
    assert p5 == 0;
}
