/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

function PowFast(x: nat, n: nat): nat
  decreases n
{
  if n == 0 then 1
  else if n % 2 == 0 then PowFast(x * x, n / 2)
  else x * PowFast(x * x, n / 2)
}

function ModPowFast(x: nat, n: nat, m: nat): nat
  requires m > 0
  decreases n
{
  if n == 0 then 1 % m
  else if n % 2 == 0 then ModPowFast((x * x) % m, n / 2, m)
  else ((x % m) * ModPowFast((x * x) % m, n / 2, m)) % m
}

lemma ModPowFastMod1(x: nat, n: nat)
  ensures ModPowFast(x, n, 1) == 0
  decreases n
{
  if n == 0 {
  } else {
    ModPowFastMod1((x * x) % 1, n / 2);
  }
}

// Keep these lemmas, but make their proofs lightweight (avoid heavy arithmetic rewrites),
// so they don't cause timeouts. Z3 handles these modular identities directly.
lemma ModMulElim(x: nat, y: nat, m: nat)
  requires m > 0
  ensures ((x % m) * y) % m == (x * y) % m
{
}

lemma ModMulElimRight(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * (y % m)) % m == (x * y) % m
{
}

lemma ModMulModElim(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (((x % m) * (y % m)) % m) == ((x * y) % m)
{
  // derive from the two elimination lemmas
  ModMulElimRight(x % m, y, m);
  ModMulElim(x, y, m);
}

 // Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.
method FastExponentiation(x: nat, n: nat) returns (p: nat)
  ensures p == PowFast(x, n)
{
    var mx: nat  := x; // remaining base
    var mn: nat := n; // remaining exponent
    p := 1; // partial result
    while mn > 0 
      invariant mn <= n
      invariant p * PowFast(mx, mn) == PowFast(x, n)
    {
        if mn % 2 == 1 {
            assert PowFast(mx, mn) == mx * PowFast(mx * mx, mn / 2);
            p := p * mx;
        } else {
            assert PowFast(mx, mn) == PowFast(mx * mx, mn / 2);
        }
        mx := mx * mx;
        mn := mn / 2;
    }
    assert PowFast(mx, 0) == 1;
    assert p * PowFast(mx, 0) == p;
}


// Iterative computation of x^n mod m in time O(log n), 
// by the fast modular exponentiation algorithm, avoiding overflows.
method FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
  requires m > 0
  ensures res == ModPowFast(x, n, m)
  ensures m > 1 ==> res < m
{
    if m == 1 {
        ModPowFastMod1(x, n);
        return 0; // x^n % 1 == 0
    }

    var mn: nat := n; // remaining exponent

    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    while mn > 0 
      decreases mn
      invariant mn <= n
      invariant 0 <= p2 < m
      invariant 0 <= mx2 < m
      invariant (p2 * ModPowFast(mx2, mn, m)) % m == ModPowFast(x, n, m)
    {
        if mn % 2 == 1 {
            assert mx2 % m == mx2;
            assert ModPowFast(mx2, mn, m) == (mx2 * ModPowFast((mx2 * mx2) % m, mn / 2, m)) % m;

            var oldP2 := p2;
            p2 := (p2 * mx2) % m;

            assert p2 < m;

            // Help the verifier relate the updated p2 to the old invariant shape
            ModMulElim(oldP2 * mx2, ModPowFast((mx2 * mx2) % m, mn / 2, m), m);
            ModMulElim(oldP2, mx2 * ModPowFast((mx2 * mx2) % m, mn / 2, m), m);
        } else {
            assert ModPowFast(mx2, mn, m) == ModPowFast((mx2 * mx2) % m, mn / 2, m);
        }

        mn := mn / 2;
        mx2 := (mx2 * mx2) % m;
        assert mx2 < m;
    }
    
    assert ModPowFast(mx2, 0, m) == 1 % m;
    assert (p2 * ModPowFast(mx2, 0, m)) % m == (p2 * (1 % m)) % m;
    assert p2 % m == p2;
    assert (p2 * (1 % m)) % m == p2;

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
