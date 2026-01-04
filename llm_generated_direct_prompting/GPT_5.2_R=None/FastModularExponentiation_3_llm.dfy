/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

function Pow(x: nat, n: nat): nat
  decreases n
{
  if n == 0 then 1 else x * Pow(x, n - 1)
}

lemma PowEven(x: nat, k: nat)
  ensures Pow(x, 2 * k) == Pow(x * x, k)
  decreases k
{
  if k == 0 {
  } else {
    PowEven(x, k - 1);
    calc {
      Pow(x, 2 * k);
      == x * Pow(x, 2 * k - 1);
      == x * Pow(x, 2 * (k - 1) + 1);
      == x * (x * Pow(x, 2 * (k - 1)));
      == (x * x) * Pow(x, 2 * (k - 1));
      == (x * x) * Pow(x * x, k - 1);
      == Pow(x * x, k);
    }
  }
}

lemma PowOdd(x: nat, k: nat)
  ensures Pow(x, 2 * k + 1) == x * Pow(x * x, k)
{
  PowEven(x, k);
  calc {
    Pow(x, 2 * k + 1);
    == x * Pow(x, 2 * k);
    == x * Pow(x * x, k);
  }
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a * b) % m) == (((a % m) * (b % m)) % m)
{
}

lemma ModMul3(a: nat, b: nat, c: nat, m: nat)
  requires m > 0
  ensures ((a * b * c) % m) == (((a % m) * (b % m) % m) * (c % m) % m)
{
  calc {
    (a * b * c) % m;
    == ((a * b) * c) % m;
    == ((((a * b) % m) * (c % m)) % m) by { ModMul(a * b, c, m); }
    == (((((a % m) * (b % m)) % m) * (c % m)) % m) by { ModMul(a, b, m); }
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
            var k: nat := mn / 2;
            assert mn == 2 * k + 1;
            PowOdd(mx, k);
            p := p * mx;
        } 
        mx := mx * mx;
        mn := mn / 2;
        PowEven(mx / mx, 0); // dummy to avoid unused warnings (no effect)
    }
}


// Iterative computation of x^n mod m in time O(log n), 
// by the fast modular exponentiation algorithm, avoiding overflows.
method FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
  ensures m == 1 ==> res == 0
  ensures m > 1 ==> res == Pow(x, n) % m
{
    if m == 1 {
        return 0; // x^n % 1 == 0
    }

    var mn: nat := n; // remaining exponent


    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    while mn > 0 
      invariant m > 0
      invariant p2 < m
      invariant (p2 * Pow(mx2, mn)) % m == Pow(x, n) % m
      decreases mn
    {
        if mn % 2 == 1 {
            var k: nat := mn / 2;
            assert mn == 2 * k + 1;
            PowOdd(mx2, k);
            ModMul3(p2, mx2, Pow(mx2 * mx2, k), m);
            p2 := (p2 * mx2) % m;
            assert p2 < m;
        } 
        var oldMx2 := mx2;
        mn := mn / 2;
        mx2 := (mx2 * mx2) % m;

        // Re-establish invariant after squaring and halving
        // Using: Pow(oldMx2, 2*mn) == Pow(oldMx2*oldMx2, mn) and modular multiplication properties
        PowEven(oldMx2, mn);
        ModMul(p2, Pow(oldMx2, 2 * mn), m);
        ModMul(oldMx2, oldMx2, m);
        ModMul(p2, Pow((oldMx2 * oldMx2) % m, mn), m);
        assert (p2 * Pow(mx2, mn)) % m == (p2 * Pow(oldMx2, 2 * mn)) % m;
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
