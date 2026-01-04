/* 
* Verification in Dafny of the fast modular exponentiation algorithm,  
* as described in https://en.wikipedia.org/wiki/Modular_exponentiation.
* It is based on the fast exponentiation algorithm.
*/

// Power function for specification purposes
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
lemma PowerMultiplication(x: nat, a: nat, b: nat)
    ensures Power(x, a * b) == Power(Power(x, a), b)
{
    if b == 0 {
    } else {
        calc {
            Power(x, a * b);
            == Power(x, a * (b - 1) + a);
            == { PowerAddition(x, a * (b - 1), a); }
               Power(x, a * (b - 1)) * Power(x, a);
            == { PowerMultiplication(x, a, b - 1); }
               Power(Power(x, a), b - 1) * Power(x, a);
            == Power(Power(x, a), b);
        }
    }
}

// Lemma for the key invariant relationship
lemma PowerDecomposition(x: nat, n: nat, p: nat, mx: nat, mn: nat)
    requires Power(mx, mn) * p == Power(x, n)
    requires mn > 0
    requires mn % 2 == 1
    ensures Power(mx * mx, mn / 2) * (p * mx) == Power(x, n)
{
    calc {
        Power(mx * mx, mn / 2) * (p * mx);
        == { PowerMultiplication(mx, 2, mn / 2); }
           Power(mx, 2 * (mn / 2)) * (p * mx);
        == Power(mx, mn - 1) * (p * mx);
        == Power(mx, mn - 1) * p * mx;
        == { PowerAddition(mx, mn - 1, 1); }
           Power(mx, mn) * p;
        == Power(x, n);
    }
}

lemma PowerDecompositionEven(x: nat, n: nat, p: nat, mx: nat, mn: nat)
    requires Power(mx, mn) * p == Power(x, n)
    requires mn > 0
    requires mn % 2 == 0
    ensures Power(mx * mx, mn / 2) * p == Power(x, n)
{
    calc {
        Power(mx * mx, mn / 2) * p;
        == { PowerMultiplication(mx, 2, mn / 2); }
           Power(mx, 2 * (mn / 2)) * p;
        == Power(mx, mn) * p;
        == Power(x, n);
    }
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
        invariant Power(mx, mn) * p == Power(x, n)
    {
        if mn % 2 == 1 {
            PowerDecomposition(x, n, p, mx, mn);
            p := p * mx;
        } else {
            PowerDecompositionEven(x, n, p, mx, mn);
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
}

// Lemma for modular power
lemma ModularPower(x: nat, n: nat, m: nat)
    requires m > 1
    ensures Power(x, n) % m == Power(x % m, n) % m
{
    if n == 0 {
    } else {
        calc {
            Power(x, n) % m;
            == (x * Power(x, n - 1)) % m;
            == { ModularMultiplication(x, Power(x, n - 1), m); }
               ((x % m) * (Power(x, n - 1) % m)) % m;
            == { ModularPower(x, n - 1, m); }
               ((x % m) * (Power(x % m, n - 1) % m)) % m;
            == { ModularMultiplication(x % m, Power(x % m, n - 1), m); }
               ((x % m) * Power(x % m, n - 1)) % m;
            == Power(x % m, n) % m;
        }
    }
}

// Lemma for the modular invariant relationship
lemma ModularPowerDecomposition(x: nat, n: nat, p2: nat, mx2: nat, mn: nat, m: nat)
    requires m > 1
    requires (Power(mx2, mn) * p2) % m == Power(x, n) % m
    requires mn > 0
    requires mn % 2 == 1
    ensures (Power((mx2 * mx2) % m, mn / 2) * ((p2 * mx2) % m)) % m == Power(x, n) % m
{
    calc {
        (Power((mx2 * mx2) % m, mn / 2) * ((p2 * mx2) % m)) % m;
        == { ModularMultiplication(Power((mx2 * mx2) % m, mn / 2), (p2 * mx2) % m, m); }
           ((Power((mx2 * mx2) % m, mn / 2) % m) * ((p2 * mx2) % m % m)) % m;
        == ((Power((mx2 * mx2) % m, mn / 2) % m) * ((p2 * mx2) % m)) % m;
        == { ModularPower(mx2 * mx2, mn / 2, m); }
           ((Power(mx2 * mx2, mn / 2) % m) * ((p2 * mx2) % m)) % m;
        == { ModularMultiplication(Power(mx2 * mx2, mn / 2), p2 * mx2, m); }
           (Power(mx2 * mx2, mn / 2) * (p2 * mx2)) % m;
        == { PowerMultiplication(mx2, 2, mn / 2); }
           (Power(mx2, 2 * (mn / 2)) * (p2 * mx2)) % m;
        == (Power(mx2, mn - 1) * (p2 * mx2)) % m;
        == (Power(mx2, mn - 1) * p2 * mx2) % m;
        == { PowerAddition(mx2, mn - 1, 1); }
           (Power(mx2, mn) * p2) % m;
        == Power(x, n) % m;
    }
}

lemma ModularPowerDecompositionEven(x: nat, n: nat, p2: nat, mx2: nat, mn: nat, m: nat)
    requires m > 1
    requires (Power(mx2, mn) * p2) % m == Power(x, n) % m
    requires mn > 0
    requires mn % 2 == 0
    ensures (Power((mx2 * mx2) % m, mn / 2) * p2) % m == Power(x, n) % m
{
    calc {
        (Power((mx2 * mx2) % m, mn / 2) * p2) % m;
        == { ModularMultiplication(Power((mx2 * mx2) % m, mn / 2), p2, m); }
           ((Power((mx2 * mx2) % m, mn / 2) % m) * (p2 % m)) % m;
        == { ModularPower(mx2 * mx2, mn / 2, m); }
           ((Power(mx2 * mx2, mn / 2) % m) * (p2 % m)) % m;
        == { ModularMultiplication(Power(mx2 * mx2, mn / 2), p2, m); }
           (Power(mx2 * mx2, mn / 2) * p2) % m;
        == { PowerMultiplication(mx2, 2, mn / 2); }
           (Power(mx2, 2 * (mn / 2)) * p2) % m;
        == (Power(mx2, mn) * p2) % m;
        == Power(x, n) % m;
    }
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

    ModularPower(x, n, m);
    
    while mn > 0 
        invariant (Power(mx2, mn) * p2) % m == Power(x, n) % m
        invariant p2 < m
        invariant mx2 < m
    {
        if mn % 2 == 1 {
            ModularPowerDecomposition(x, n, p2, mx2, mn, m);
            p2 := (p2 * mx2) % m;
        } else {
            ModularPowerDecompositionEven(x, n, p2, mx2, mn, m);
        }
        mn := mn / 2;
        mx2 := (mx2 * mx2) % m;
    }
    
    return p2;
}




// A few test cases (checked statically by Dafny).
method TestModularExponentiation() {
    var p1 := FastExponentiation(2, 10);
    assert Power(2, 10) == 2 * Power(2, 9);
    assert Power(2, 9) == 2 * Power(2, 8);
    assert Power(2, 8) == 2 * Power(2, 7);
    assert Power(2, 7) == 2 * Power(2, 6);
    assert Power(2, 6) == 2 * Power(2, 5);
    assert Power(2, 5) == 2 * Power(2, 4);
    assert Power(2, 4) == 2 * Power(2, 3);
    assert Power(2, 3) == 2 * Power(2, 2);
    assert Power(2, 2) == 2 * Power(2, 1);
    assert Power(2, 1) == 2 * Power(2, 0);
    assert Power(2, 0) == 1;
    assert p1 == 1024;

    var p2 := FastModularExponentiation(2, 10, 7);
    assert p2 == 2;

    var p3 := FastExponentiation(10, 6);
    assert Power(10, 6) == 10 * Power(10, 5);
    assert Power(10, 5) == 10 * Power(10, 4);
    assert Power(10, 4) == 10 * Power(10, 3);
    assert Power(10, 3) == 10 * Power(10, 2);
    assert Power(10, 2) == 10 * Power(10, 1);
    assert Power(10, 1) == 10 * Power(10, 0);
    assert Power(10, 0) == 1;
    assert p3 == 1000000;

    var p4 := FastModularExponentiation(10, 6, 9);
    assert p4 == 1;

    var p5 := FastModularExponentiation(1000, 1000, 1);
    assert p5 == 0;
}
