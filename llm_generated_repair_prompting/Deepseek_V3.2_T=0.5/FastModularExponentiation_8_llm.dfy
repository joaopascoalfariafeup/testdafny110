/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.
method FastExponentiation(x: nat, n: nat) returns (p: nat)
  ensures p == Power(x, n)
{
    var mx: nat  := x; // remaining base
    var mn: nat := n; // remaining exponent
    p := 1; // partial result
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

function Power(x: nat, n: nat): nat
  decreases n
{
  if n == 0 then 1 else x * Power(x, n-1)
}

// Helper function for exponentiation by squaring
function Power2(x: nat, k: nat): nat
  decreases k
{
  if k == 0 then 1 else Power2(x, k-1) * x
}

// Lemma to help prove properties about Power and Power2
lemma PowerLemma(x: nat, n: nat, k: nat)
  ensures Power(x, n + k) == Power(x, n) * Power(x, k)
  decreases n
{
  if n == 0 {
    // base case
  } else {
    PowerLemma(x, n-1, k);
  }
}

lemma Power2Lemma(x: nat, k: nat)
  ensures Power(x, Power2(2, k)) == Power(Power(x, 1), Power2(2, k))
  decreases k
{
  if k == 0 {
    // base case
  } else {
    Power2Lemma(x, k-1);
    // Additional proof about squaring
    calc {
      Power(x, Power2(2, k));
      == { assert Power2(2, k) == 2 * Power2(2, k-1); }
      Power(x, 2 * Power2(2, k-1));
      == { PowerLemma(x, Power2(2, k-1), Power2(2, k-1)); }
      Power(x, Power2(2, k-1)) * Power(x, Power2(2, k-1));
      == { Power2Lemma(x, k-1); }
      Power(Power(x, 1), Power2(2, k-1)) * Power(Power(x, 1), Power2(2, k-1));
      == { PowerLemma(Power(x, 1), Power2(2, k-1), Power2(2, k-1)); }
      Power(Power(x, 1), 2 * Power2(2, k-1));
      == { assert 2 * Power2(2, k-1) == Power2(2, k); }
      Power(Power(x, 1), Power2(2, k));
    }
  }
}

// Function to compute 2^k for nat k
function TwoToThe(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * TwoToThe(k-1)
}

// Lemma about TwoToThe
lemma TwoToTheLemma(k: nat)
  ensures TwoToThe(k) == Power2(2, k)
  decreases k
{
  if k == 0 {
  } else {
    TwoToTheLemma(k-1);
  }
}

// Lemma about Power and multiplication
lemma PowerMulLemma(x: nat, a: nat, b: nat)
  ensures Power(x, a + b) == Power(x, a) * Power(x, b)
  decreases a
{
  if a == 0 {
  } else {
    PowerMulLemma(x, a-1, b);
  }
}

// Lemma about Power and squaring
lemma PowerSquareLemma(x: nat, k: nat)
  ensures Power(x, 2*k) == Power(x, k) * Power(x, k)
  decreases k
{
  if k == 0 {
  } else {
    PowerSquareLemma(x, k-1);
  }
}

// Iterative computation of x^n mod m in time O(log n), 
// by the fast modular exponentiation algorithm, avoiding overflows.
method FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
  requires m > 0
  ensures res == Power(x, n) % m
{
    if m == 1 {
        res := 0;
        return;
    }

    var mn: nat := n; // remaining exponent
    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m
    var p2 : nat := 1; // partial result for computing Power(x, n) % m

    while mn > 0 
      invariant p2 == Power(x, n - mn) % m
      invariant mx2 == Power(x, TwoToThe(n - mn)) % m
      invariant 0 <= p2 < m
      invariant 0 <= mx2 < m
      decreases mn
    {
        if mn % 2 == 1 {
            p2 := (p2 * mx2) % m;
            // Helper assertion
            assert Power(x, n - mn + 1) % m == (Power(x, n - mn) * Power(x, 1)) % m;
        } 
        mn := mn / 2;
        mx2 := (mx2 * mx2) % m;
        // Helper assertion for the update
        assert Power(x, TwoToThe(n - mn)) % m == (Power(x, TwoToThe(n - mn - 1)) * Power(x, TwoToThe(n - mn - 1))) % m;
    }
    
    res := p2;
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



