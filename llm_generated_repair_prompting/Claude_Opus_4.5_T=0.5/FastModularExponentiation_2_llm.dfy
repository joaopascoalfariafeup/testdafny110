/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

// Power function for specification
ghost function Power(x: nat, n: nat): nat
{
    if n == 0 then 1
    else x * Power(x, n - 1)
}

// Lemma: Power(x, a + b) == Power(x, a) * Power(x, b)
lemma PowerAddition(x: nat, a: nat, b: nat)
    ensures Power(x, a + b) == Power(x, a) * Power(x, b)
{
    if a == 0 {
    } else {
        PowerAddition(x, a - 1, b);
    }
}

// Lemma: Power(x, a * b) == Power(Power(x, a), b)
lemma {:induction b} PowerMultiplication(x: nat, a: nat, b: nat)
    ensures Power(x, a * b) == Power(Power(x, a), b)
{
    if b == 0 {
        assert a * b == 0;
    } else {
        PowerMultiplication(x, a, b - 1);
        assert a * b == a * (b - 1) + a;
        PowerAddition(x, a * (b - 1), a);
    }
}

// Lemma for the key invariant relationship
lemma PowerDecomposition(mx: nat, mn: nat, p: nat, x: nat, n: nat)
    requires p * Power(mx, mn) == Power(x, n)
    requires mn > 0
    requires mn % 2 == 1
    ensures (p * mx) * Power(mx * mx, mn / 2) == Power(x, n)
{
    assert mn == 2 * (mn / 2) + 1;
    PowerMultiplication(mx, 2, mn / 2);
    assert Power(mx * mx, mn / 2) == Power(mx, 2 * (mn / 2));
    assert mn - 1 == 2 * (mn / 2);
    PowerAddition(mx, 1, mn - 1);
    assert mx * Power(mx, mn - 1) == Power(mx, mn);
}

lemma PowerDecompositionEven(mx: nat, mn: nat, p: nat, x: nat, n: nat)
    requires p * Power(mx, mn) == Power(x, n)
    requires mn > 0
    requires mn % 2 == 0
    ensures p * Power(mx * mx, mn / 2) == Power(x, n)
{
    assert mn == 2 * (mn / 2);
    PowerMultiplication(mx, 2, mn / 2);
    assert Power(mx * mx, mn / 2) == Power(mx, 2 * (mn / 2));
    assert Power(mx * mx, mn / 2) == Power(mx, mn);
}

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
    {
        if mn % 2 == 1 {
            PowerDecomposition(mx, mn, p, x, n);
            p := p * mx;
        } else {
            PowerDecompositionEven(mx, mn, p, x, n);
        }
        mx := mx * mx;
        mn := mn / 2;
    }
}

// Lemma for modular arithmetic
lemma ModularMultiplication(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    // This is a basic property of modular arithmetic that Dafny can prove
}

// Lemma: Power(x, n) % m == Power(x % m, n) % m
lemma {:induction n} PowerMod(x: nat, n: nat, m: nat)
    requires m > 1
    ensures Power(x, n) % m == Power(x % m, n) % m
{
    if n == 0 {
    } else {
        PowerMod(x, n - 1, m);
        ModularMultiplication(x, Power(x, n - 1), m);
        ModularMultiplication(x % m, Power(x % m, n - 1), m);
    }
}

// Helper lemma for the odd case
lemma OddCaseHelper(p2: nat, mx2: nat, mn: nat, x: nat, n: nat, m: nat)
    requires m > 1
    requires mn > 0
    requires mn % 2 == 1
    requires (p2 * Power(mx2, mn)) % m == Power(x % m, n) % m
    ensures ((p2 * mx2) % m * Power((mx2 * mx2) % m, mn / 2)) % m == Power(x % m, n) % m
{
    var newP := (p2 * mx2) % m;
    var newMx := (mx2 * mx2) % m;
    var newMn := mn / 2;
    
    PowerMod(mx2 * mx2, newMn, m);
    assert Power(newMx, newMn) % m == Power(mx2 * mx2, newMn) % m;
    
    PowerMultiplication(mx2, 2, newMn);
    assert Power(mx2 * mx2, newMn) == Power(mx2, 2 * newMn);
    
    assert mn == 2 * newMn + 1;
    assert mn - 1 == 2 * newMn;
    
    PowerAddition(mx2, 1, mn - 1);
    assert Power(mx2, mn) == mx2 * Power(mx2, mn - 1);
    assert Power(mx2, mn - 1) == Power(mx2, 2 * newMn);
    assert Power(mx2, mn) == mx2 * Power(mx2 * mx2, newMn);
    
    assert (p2 * Power(mx2, mn)) % m == (p2 * mx2 * Power(mx2 * mx2, newMn)) % m;
    
    ModularMultiplication(p2 * mx2, Power(mx2 * mx2, newMn), m);
    ModularMultiplication(newP, Power(newMx, newMn), m);
}

// Helper lemma for the even case
lemma EvenCaseHelper(p2: nat, mx2: nat, mn: nat, x: nat, n: nat, m: nat)
    requires m > 1
    requires mn > 0
    requires mn % 2 == 0
    requires (p2 * Power(mx2, mn)) % m == Power(x % m, n) % m
    ensures (p2 * Power((mx2 * mx2) % m, mn / 2)) % m == Power(x % m, n) % m
{
    var newMx := (mx2 * mx2) % m;
    var newMn := mn / 2;
    
    PowerMod(mx2 * mx2, newMn, m);
    assert Power(newMx, newMn) % m == Power(mx2 * mx2, newMn) % m;
    
    PowerMultiplication(mx2, 2, newMn);
    assert Power(mx2 * mx2, newMn) == Power(mx2, 2 * newMn);
    
    assert mn == 2 * newMn;
    assert Power(mx2 * mx2, newMn) == Power(mx2, mn);
    
    ModularMultiplication(p2, Power(mx2 * mx2, newMn), m);
    ModularMultiplication(p2, Power(newMx, newMn), m);
}

// Iterative computation of x^n mod m in time O(log n), 
// by the fast modular exponentiation algorithm, avoiding overflows.
method FastModularExponentiation(x: nat, n: nat, m: nat) returns (res: nat) 
    requires m >= 1
    ensures res == Power(x, n) % m
{
    if m == 1 {
        return 0; // x^n % 1 == 0
    }

    var mn: nat := n; // remaining exponent

    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    while mn > 0 
        invariant (p2 * Power(mx2, mn)) % m == Power(x % m, n) % m
        invariant p2 < m
        invariant mx2 < m
    {
        if mn % 2 == 1 {
            OddCaseHelper(p2, mx2, mn, x, n, m);
            p2 := (p2 * mx2) % m;
        } else {
            EvenCaseHelper(p2, mx2, mn, x, n, m);
        }
        mn := mn / 2;
        mx2 := (mx2 * mx2) % m;
    }
    
    PowerMod(x, n, m);
    return p2;
}




// A few test cases (checked statically by Dafny).
method {:fuel Power, 11} TestModularExponentiation() {
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
