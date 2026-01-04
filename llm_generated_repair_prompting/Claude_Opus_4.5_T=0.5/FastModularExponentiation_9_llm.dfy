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

// Helper lemma for Power(x, 2) == x * x
lemma PowerTwo(x: nat)
    ensures Power(x, 2) == x * x
{
    assert Power(x, 2) == x * Power(x, 1);
    assert Power(x, 1) == x * Power(x, 0);
    assert Power(x, 0) == 1;
}

// Lemma for the key invariant relationship
lemma PowerDecomposition(mx: nat, mn: nat, p: nat, x: nat, n: nat)
    requires p * Power(mx, mn) == Power(x, n)
    requires mn > 0
    requires mn % 2 == 1
    ensures (p * mx) * Power(mx * mx, mn / 2) == Power(x, n)
{
    var half := mn / 2;
    assert mn == 2 * half + 1;
    
    PowerMultiplication(mx, 2, half);
    
    PowerAddition(mx, 1, 2 * half);
    assert Power(mx, mn) == mx * Power(mx, 2 * half);
    assert Power(mx, 2 * half) == Power(mx * mx, half);
    
    calc {
        (p * mx) * Power(mx * mx, half);
        == p * mx * Power(mx * mx, half);
        == p * (mx * Power(mx * mx, half));
        == p * (mx * Power(mx, 2 * half));
        == p * Power(mx, mn);
        == Power(x, n);
    }
}

lemma PowerDecompositionEven(mx: nat, mn: nat, p: nat, x: nat, n: nat)
    requires p * Power(mx, mn) == Power(x, n)
    requires mn > 0
    requires mn % 2 == 0
    ensures p * Power(mx * mx, mn / 2) == Power(x, n)
{
    var half := mn / 2;
    assert mn == 2 * half;
    PowerMultiplication(mx, 2, half);
    assert Power(mx, 2 * half) == Power(Power(mx, 2), half);
    PowerTwo(mx);
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

// Helper lemma: any multiple of m has remainder 0
lemma MultipleModZero(k: nat, m: nat)
    requires m > 1
    ensures (k * m) % m == 0
{
}

// Lemma for modular arithmetic
lemma {:induction false} ModularMultiplication(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    var qa := a / m;
    var ra := a % m;
    var qb := b / m;
    var rb := b % m;
    
    assert a == qa * m + ra;
    assert b == qb * m + rb;
    
    calc {
        (a * b) % m;
        == ((qa * m + ra) * b) % m;
        == (qa * m * b + ra * b) % m;
        == { MultipleModZero(qa * b, m); assert (qa * m * b) % m == 0; }
        (ra * b) % m;
        == (ra * (qb * m + rb)) % m;
        == (ra * qb * m + ra * rb) % m;
        == { MultipleModZero(ra * qb, m); assert (ra * qb * m) % m == 0; }
        (ra * rb) % m;
        == ((a % m) * (b % m)) % m;
    }
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

// Helper lemma for the odd case - simplified
lemma OddCaseHelper(p2: nat, mx2: nat, mn: nat, x: nat, n: nat, m: nat)
    requires m > 1
    requires mn > 0
    requires mn % 2 == 1
    requires (p2 * Power(mx2, mn)) % m == Power(x % m, n) % m
    ensures ((p2 * mx2) % m * Power((mx2 * mx2) % m, mn / 2)) % m == Power(x % m, n) % m
{
    var newMn := mn / 2;
    assert mn == 2 * newMn + 1;
    
    PowerMultiplication(mx2, 2, newMn);
    PowerAddition(mx2, 1, 2 * newMn);
    assert Power(mx2, mn) == mx2 * Power(mx2 * mx2, newMn);
    
    // p2 * Power(mx2, mn) == p2 * mx2 * Power(mx2 * mx2, newMn)
    assert p2 * Power(mx2, mn) == p2 * mx2 * Power(mx2 * mx2, newMn);
    
    PowerMod(mx2 * mx2, newMn, m);
    assert Power(mx2 * mx2, newMn) % m == Power((mx2 * mx2) % m, newMn) % m;
    
    ModularMultiplication(p2 * mx2, Power(mx2 * mx2, newMn), m);
    ModularMultiplication((p2 * mx2) % m, Power((mx2 * mx2) % m, newMn), m);
}

// Helper lemma for the even case - simplified
lemma EvenCaseHelper(p2: nat, mx2: nat, mn: nat, x: nat, n: nat, m: nat)
    requires m > 1
    requires mn > 0
    requires mn % 2 == 0
    requires (p2 * Power(mx2, mn)) % m == Power(x % m, n) % m
    ensures (p2 * Power((mx2 * mx2) % m, mn / 2)) % m == Power(x % m, n) % m
{
    var newMn := mn / 2;
    assert mn == 2 * newMn;
    
    PowerMultiplication(mx2, 2, newMn);
    assert Power(mx2, mn) == Power(mx2 * mx2, newMn);
    
    PowerMod(mx2 * mx2, newMn, m);
    assert Power(mx2 * mx2, newMn) % m == Power((mx2 * mx2) % m, newMn) % m;
    
    ModularMultiplication(p2, Power(mx2 * mx2, newMn), m);
    ModularMultiplication(p2, Power((mx2 * mx2) % m, newMn), m);
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
