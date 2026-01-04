/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

// Keep fuels modest to avoid SMT blowups, but large enough for the tests.
function {:fuel 8} PowFast(x: nat, n: nat): nat
  decreases n
{
  if n == 0 then 1
  else if n % 2 == 0 then PowFast(x * x, n / 2)
  else x * PowFast(x * x, n / 2)
}

function {:fuel 12} ModPowFast(x: nat, n: nat, m: nat): nat
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

// Useful bound: for m > 1, the result of ModPowFast is always < m
lemma ModPowFastLtM(x: nat, n: nat, m: nat)
  requires m > 1
  ensures ModPowFast(x, n, m) < m
  decreases n
{
  if n == 0 {
    // 1 % m is always < m when m > 0 (and in particular when m > 1)
  } else if n % 2 == 0 {
    ModPowFastLtM((x * x) % m, n / 2, m);
  } else {
    ModPowFastLtM((x * x) % m, n / 2, m);
    // a % m < m for m > 0
  }
}

// --- Small arithmetic helpers for modular multiplication (proved for nat) ---

lemma NatMulLe(a: nat, b: nat, m: nat)
  requires a <= b
  requires m > 0
  ensures a * m <= b * m
{
  var d := b - a;
  assert b == a + d;

  calc {
    b * m;
    == (a + d) * m;
    == a * m + d * m;
    >= a * m;
  }
}

lemma NatDivModUnique(x: nat, m: nat, q: nat, r: nat)
  requires m > 0
  requires x == q * m + r
  requires r < m
  ensures q == x / m
  ensures r == x % m
{
  var q2 := x / m;
  var r2 := x % m;

  // Dafny's built-in division algorithm facts
  assert x == q2 * m + r2;
  assert r2 < m;

  // Show q == q2 by ruling out q < q2 and q > q2
  if q < q2 {
    // From q < q2 over nat
    assert q + 1 <= q2;

    // Use r < m to bound q*m + r < (q+1)*m
    assert q * m + r < q * m + m;
    assert q * m + m == (q + 1) * m;

    // Monotonicity of multiplication by positive m
    NatMulLe(q + 1, q2, m);
    assert (q + 1) * m <= q2 * m;

    // Chain to contradict x == q*m+r == q2*m+r2
    assert q * m + r < q2 * m;
    assert q2 * m <= q2 * m + r2;
    assert q * m + r < q2 * m + r2;
    assert false;
  }
  if q2 < q {
    assert q2 + 1 <= q;

    assert q2 * m + r2 < q2 * m + m;
    assert q2 * m + m == (q2 + 1) * m;

    NatMulLe(q2 + 1, q, m);
    assert (q2 + 1) * m <= q * m;

    assert q2 * m + r2 < q * m;
    assert q * m <= q * m + r;
    assert q2 * m + r2 < q * m + r;
    assert false;
  }

  assert q == q2;
  // Then r must match as well
  assert r == r2;
}

lemma NatModAddMultiple(b: nat, t: nat, m: nat)
  requires m > 0
  ensures (b + m * t) % m == b % m
{
  var q := b / m;
  var r := b % m;
  assert b == q * m + r;
  assert r < m;

  var x := b + m * t;
  assert x == (q + t) * m + r;

  NatDivModUnique(x, m, q + t, r);
  assert x % m == r;
}

lemma NatModMulElim(x: nat, y: nat, m: nat)
  requires m > 0
  ensures ((x % m) * y) % m == (x * y) % m
{
  var q := x / m;
  var r := x % m;
  assert x == q * m + r;
  assert r < m;

  assert x * y == (q * m + r) * y;
  assert (q * m + r) * y == (q * y) * m + r * y;

  // (x*y) % m = ((q*y)*m + r*y) % m = (r*y) % m
  NatModAddMultiple(r * y, q * y, m);
  assert (r * y + m * (q * y)) % m == (r * y) % m;

  // rewrite m*(q*y) as (q*y)*m
  assert r * y + m * (q * y) == (q * y) * m + r * y;

  assert (x * y) % m == (r * y) % m;
  assert ((x % m) * y) % m == (r * y) % m;
}

lemma NatModMulElimRight(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * (y % m)) % m == (x * y) % m
{
  // Symmetric to NatModMulElim, just swap roles of x and y in the proof idea
  var q := y / m;
  var r := y % m;
  assert y == q * m + r;
  assert r < m;

  assert x * y == x * (q * m + r);
  assert x * (q * m + r) == (x * q) * m + x * r;

  NatModAddMultiple(x * r, x * q, m);
  assert (x * r + m * (x * q)) % m == (x * r) % m;

  assert x * r + m * (x * q) == (x * q) * m + x * r;

  assert (x * y) % m == (x * r) % m;
  assert (x * (y % m)) % m == (x * r) % m;
}

lemma ModMulElim(x: nat, y: nat, m: nat)
  requires m > 0
  ensures ((x % m) * y) % m == (x * y) % m
{
  NatModMulElim(x, y, m);
}

lemma ModMulElimRight(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * (y % m)) % m == (x * y) % m
{
  NatModMulElimRight(x, y, m);
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
      decreases mn
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
method {:timeLimit 2000} FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
  requires m > 0
  ensures res == ModPowFast(x, n, m)
  ensures m > 1 ==> res < m
{
    if m == 1 {
        ModPowFastMod1(x, n);
        return 0; // x^n % 1 == 0
    }
    assert m > 1;

    var mn: nat := n; // remaining exponent

    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    // Helpful facts before entering the loop (keeps the loop proof lightweight)
    assert mx2 < m;
    assert p2 < m;

    while mn > 0 
      decreases mn
      invariant m > 1
      invariant mn <= n
      invariant p2 < m
      invariant mx2 < m
      invariant (p2 * ModPowFast(mx2, mn, m)) % m == ModPowFast(x, n, m)
    {
        if mn % 2 == 1 {
            assert mx2 % m == mx2;
            assert ModPowFast(mx2, mn, m) == (mx2 * ModPowFast((mx2 * mx2) % m, mn / 2, m)) % m;

            var oldP2 := p2;
            var t := ModPowFast((mx2 * mx2) % m, mn / 2, m);

            // Update p2
            p2 := (p2 * mx2) % m;
            assert p2 < m;

            // Preserve the invariant with a direct normalization to (oldP2*mx2*t) % m
            // newLHS == ((oldP2*mx2)%m * t) % m == (oldP2*mx2*t) % m
            ModMulElim(oldP2 * mx2, t, m);

            // oldLHS == (oldP2 * ((mx2*t)%m)) % m == (oldP2*(mx2*t)) % m
            ModMulElimRight(oldP2, mx2 * t, m);
            assert (oldP2 * ((mx2 * t) % m)) % m == (oldP2 * (mx2 * t)) % m;

            // Associate
            assert (oldP2 * (mx2 * t)) == ((oldP2 * mx2) * t);
        } else {
            assert ModPowFast(mx2, mn, m) == ModPowFast((mx2 * mx2) % m, mn / 2, m);
        }

        mn := mn / 2;
        mx2 := (mx2 * mx2) % m;
        assert mx2 < m;
    }
    
    assert ModPowFast(mx2, 0, m) == 1 % m;
    assert (p2 * ModPowFast(mx2, 0, m)) % m == (p2 * (1 % m)) % m;
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
