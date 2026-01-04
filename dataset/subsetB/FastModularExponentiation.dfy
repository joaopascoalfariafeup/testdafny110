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
        invariant Power(x, n) == p * Power(mx, mn) 
    {
        PowerLemma(mx, mn / 2); // helper
        if mn % 2 == 1 {
            p := p * mx;
        } 
        mx := mx * mx;
        mn := mn / 2;
    }
}

// Recursive definition of x^n.
ghost function Power(x: nat, n: nat) : (p: nat) {
    if n == 0 then 1 else x * Power(x, n-1)
}

// Iterative computation of x^n mod m in time O(log n), 
// by the fast modular exponentiation algorithm, avoiding overflows.
method FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
    requires m > 0
    ensures res == Power(x, n) % m
{
    if m == 1 {
        return 0; // x^n % 1 == 0
    }

    var mn: nat := n; // remaining exponent

    ghost var mx: nat := x; // helper: remaining base for computing Power(x, n) (ghost)
    ghost var p : nat := 1; // helper: partial result for computing Power(x, n) (ghost)

    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    while mn > 0 
        invariant Power(x, n) == p * Power(mx, mn)
        invariant p2 == p % m
        invariant mx2 == mx % m
    {
        PowerLemma(mx, mn / 2); // helper
        if mn % 2 == 1 {
            ModLemma(p, mx, m); //helper ==> (p * mx) % m == ((p % m) * (mx % m)) % m == (p2 * mx2) % m
            p := p * mx; // helper
            p2 := (p2 * mx2) % m;
        } 
        mn := mn / 2;
        ModLemma(mx, mx, m); // helper ==> (mx * mx) % m == ((mx % m) * (mx % m)) % m == (mx2 * mx2) % m
        mx := mx * mx; // helper
        mx2 := (mx2 * mx2) % m;
    }
    
    return p2;
}

// State and prove (by automatic induction on 'n') the property: x^(2n) = (x^2)^n.
lemma {:induction n} PowerLemma(x: nat, n: nat) 
  ensures Power(x, 2 * n) == Power(x * x, n) 
{    
}

// State and prove the property: (a * b) % m == ((a % m) * (b % m)) % m, with m > 0
lemma ModLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    var q1 := a / m;
    var r1 := a % m;
    assert a == q1 * m + r1;

    var q2 := b / m;
    var r2 := b % m;
    assert b == q2 * m + r2;

    var q := q1 * q2 * m + q1 * r2 + q2 * r1;
    var r := r1 * r2;
    assert a * b == q * m + r;
    ModLemma2(q, r, m); // ==> (a * b) % m == (q * m + r) % m == r % m
 }

// State and prove the property: (q * m + r) % m == r % m, with m > 0.
lemma ModLemma2(q: nat, r: nat, m: nat)
  requires m > 0 
  ensures (q * m + r) % m == r % m
{
    var q1 := (q * m + r) / m;
    var r1 := (q * m + r) % m;
    assert q * m + r == q1 * m + r1 && 0 <= r1 < m;

    var q2 := r / m;
    var r2 := r % m;
    assert r == q2 * m + r2 && 0 <= r2 < m;
    
    assert 0 - m < r1 - r2 == (q2 - q1 + q) * m < m; // combining the previous assertions
    ProdLemma(q2 - q1 + q, m); // ==> r1 - r2 == 0
}

// Proves (automatically) that |a| * b >= b when |a| > 0.
lemma ProdLemma(a: int, b: nat)
 ensures a > 0 ==> a * b >= b
 ensures a < 0 ==> a * b <= b
{ 
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