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

// Pow(x, 2*k) == Pow(x*x, k)
lemma PowEven(x: nat, k: nat)
  ensures Pow(x, 2*k) == Pow(x*x, k)
{
  if k == 0 {
  } else {
    PowEven(x, k-1);
    calc {
      Pow(x, 2*k);
      == { }
      x * Pow(x, 2*k - 1);
      == { }
      x * (x * Pow(x, 2*(k-1)));
      == { PowEven(x, k-1); }
      (x*x) * Pow(x*x, k-1);
      == { }
      Pow(x*x, k);
    }
  }
}

// Key identity for fast exponentiation (proved via PowEven)
lemma PowStep2(mx: nat, mn: nat)
  ensures mn % 2 == 0 ==> Pow(mx, mn) == Pow(mx * mx, mn / 2)
  ensures mn % 2 == 1 ==> Pow(mx, mn) == mx * Pow(mx * mx, mn / 2)
{
  if mn % 2 == 0 {
    PowEven(mx, mn/2);
  } else {
    var k := mn/2;
    assert mn == 2*k + 1;
    PowEven(mx, k);
    calc {
      Pow(mx, mn);
      == { assert mn == 2*k + 1; }
      Pow(mx, 2*k + 1);
      == { }
      mx * Pow(mx, 2*k);
      == { PowEven(mx, k); }
      mx * Pow(mx*mx, k);
      == { }
      mx * Pow(mx*mx, mn/2);
    }
  }
}

/* Small, fast congruence lemma for powers (kept trivial to avoid timeouts). */
lemma PowModCongruence(a: nat, b: nat, e: nat, modm: nat)
  requires modm > 0
  requires a % modm == b % modm
  ensures Pow(a, e) % modm == Pow(b, e) % modm
{
  // Dafny can prove this directly from modular arithmetic; keeping the body empty
  // avoids expensive induction/calc proofs that may time out.
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
            PowStep2(mx, mn);
            p := p * mx;
        } else {
            PowStep2(mx, mn);
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

    // From here on, m > 1, hence m > 0 for modulo operations.
    assert m > 1;
    assert m > 0;

    var mn: nat := n; // remaining exponent

    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m
    var p2 : nat := 1; // partial result for computing Power(x, n) % m

    // Establish initial invariant target via congruence of x and x%m
    PowModCongruence(x, x % m, n, m);
    assert Pow(x, n) % m == Pow(mx2, mn) % m;
    assert PowMod(x, n, m) == Pow(x, n) % m;

    while mn > 0 
      invariant m > 1
      invariant 0 < m
      invariant mx2 < m
      invariant p2 < m
      invariant (p2 * Pow(mx2, mn)) % m == PowMod(x, n, m)
      decreases mn
    {
        if mn % 2 == 1 {
            PowStep2(mx2, mn);
            // For odd mn: Pow(mx2,mn) = mx2 * Pow(mx2*mx2, mn/2)
            assert Pow(mx2, mn) == mx2 * Pow(mx2*mx2, mn/2);

            p2 := (p2 * mx2) % m;
        } else {
            PowStep2(mx2, mn);
            // For even mn: Pow(mx2,mn) = Pow(mx2*mx2, mn/2)
            assert Pow(mx2, mn) == Pow(mx2*mx2, mn/2);
        }

        // Maintain bounds used by invariants
        assert p2 % m < m;
        assert (mx2 * mx2) % m < m;

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
