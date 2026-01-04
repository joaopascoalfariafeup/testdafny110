/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

function Pow(x: nat, n: nat): nat
{
  if n == 0 then 1 else x * Pow(x, n - 1)
}

lemma PowEven(x: nat, k: nat)
  ensures Pow(x, 2 * k) == Pow(x * x, k)
{
  if k == 0 {
  } else {
    PowEven(x, k - 1);
    calc {
      Pow(x, 2 * k);
      == { }
      x * Pow(x, 2 * k - 1);
      == { }
      x * Pow(x, 2 * (k - 1) + 1);
      == { }
      x * (x * Pow(x, 2 * (k - 1)));
      == { PowEven(x, k - 1) }
      x * (x * Pow(x * x, k - 1));
      == { }
      (x * x) * Pow(x * x, k - 1);
      == { }
      Pow(x * x, k);
    }
  }
}

lemma PowOdd(x: nat, k: nat)
  ensures Pow(x, 2 * k + 1) == x * Pow(x * x, k)
{
  PowEven(x, k);
  calc {
    Pow(x, 2 * k + 1);
    == { }
    x * Pow(x, 2 * k);
    == { PowEven(x, k) }
    x * Pow(x * x, k);
  }
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
            PowOdd(mx, mn / 2);
            assert Pow(mx, mn) == mx * Pow(mx * mx, mn / 2);
        } else {
            PowEven(mx, mn / 2);
            assert Pow(mx, mn) == Pow(mx * mx, mn / 2);
        }
        mx := mx * mx;
        mn := mn / 2;
    }
    assert Pow(mx, 0) == 1;
}


// Iterative computation of x^n mod m in time O(log n), 
// by the fast modular exponentiation algorithm, avoiding overflows.
method FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
  requires m > 0
  ensures res < m
{
    if m == 1 {
        return 0; // x^n % 1 == 0
    }

    var mn: nat := n; // remaining exponent


    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    while mn > 0 
      invariant 0 < m
      invariant p2 < m
      invariant mx2 < m
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
