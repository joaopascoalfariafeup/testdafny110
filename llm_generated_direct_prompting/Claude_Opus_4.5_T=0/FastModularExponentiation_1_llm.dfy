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

// Lemma: Power(x * x, n) == Power(x, 2 * n)
lemma PowerSquare(x: nat, n: nat)
    ensures Power(x * x, n) == Power(x, 2 * n)
{
    if n == 0 {
    } else {
        PowerSquare(x, n - 1);
        calc {
            Power(x * x, n);
            == (x * x) * Power(x * x, n - 1);
            == (x * x) * Power(x, 2 * (n - 1));
            == x * x * Power(x, 2 * n - 2);
        }
        PowerAddition(x, 2, 2 * n - 2);
        assert Power(x, 2) == x * x;
    }
}

// Lemma for modular arithmetic: (a * b) % m == ((a % m) * (b % m)) % m
lemma ModMult(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

// Lemma: (a % m) % m == a % m
lemma ModMod(a: nat, m: nat)
    requires m > 0
    ensures (a % m) % m == a % m
{
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
            calc {
                p * mx * Power(mx, mn - 1);
                == p * mx * Power(mx, mn - 1);
            }
            assert Power(mx, mn) == mx * Power(mx, mn - 1);
            p := p * mx;
        } 
        PowerSquare(mx, mn / 2);
        mx := mx * mx;
        mn := mn / 2;
    }
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


    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (is the same as p % m)

    while mn > 0 
        invariant (p2 * Power(mx2, mn)) % m == Power(x, n) % m
        invariant p2 < m
        invariant mx2 < m
    {
        if mn % 2 == 1 {
            assert Power(mx2, mn) == mx2 * Power(mx2, mn - 1);
            calc {
                ((p2 * mx2) % m * Power(mx2, mn - 1)) % m;
                == { ModMult(p2 * mx2, Power(mx2, mn - 1), m); }
                ((p2 * mx2) * Power(mx2, mn - 1)) % m;
                == (p2 * (mx2 * Power(mx2, mn - 1))) % m;
                == (p2 * Power(mx2, mn)) % m;
            }
            p2 := (p2 * mx2) % m;
        } 
        mn := mn / 2;
        PowerSquare(mx2, mn);
        calc {
            (p2 * Power((mx2 * mx2) % m, mn)) % m;
            == { ModMult(p2, Power((mx2 * mx2) % m, mn), m); }
            ((p2 % m) * (Power((mx2 * mx2) % m, mn) % m)) % m;
        }
        ghost var oldmx2 := mx2;
        mx2 := (mx2 * mx2) % m;
        
        // Need to show Power(mx2, mn) % m == Power(oldmx2 * oldmx2, mn) % m
        assert mx2 == (oldmx2 * oldmx2) % m;
        PowerModLemma(oldmx2 * oldmx2, mn, m);
    }
    
    return p2;
}

// Lemma: Power(a % m, n) % m == Power(a, n) % m
lemma PowerModLemma(a: nat, n: nat, m: nat)
    requires m > 1
    ensures Power(a % m, n) % m == Power(a, n) % m
{
    if n == 0 {
    } else {
        calc {
            Power(a % m, n) % m;
            == ((a % m) * Power(a % m, n - 1)) % m;
            == { ModMult(a % m, Power(a % m, n - 1), m); }
            (((a % m) % m) * (Power(a % m, n - 1) % m)) % m;
            == { ModMod(a, m); }
            ((a % m) * (Power(a % m, n - 1) % m)) % m;
            == { PowerModLemma(a, n - 1, m); }
            ((a % m) * (Power(a, n - 1) % m)) % m;
            == { ModMult(a, Power(a, n - 1), m); }
            (a * Power(a, n - 1)) % m;
            == Power(a, n) % m;
        }
    }
}


// A few test cases (checked statically by Dafny).
method {:fuel Power, 11} TestModularExponentiation() {
    var p1 := FastExponentiation(2, 10);
    assert Power(2, 10) == 1024;
    assert p1 == 1024;

    var p2 := FastModularExponentiation(2, 10, 7);
    assert Power(2, 10) == 1024;
    assert 1024 % 7 == 2;
    assert p2 == 2;

    var p3 := FastExponentiation(10, 6);
    assert Power(10, 6) == 1000000;
    assert p3 == 1000000;

    var p4 := FastModularExponentiation(10, 6, 9);
    assert Power(10, 6) == 1000000;
    assert 1000000 % 9 == 1;
    assert p4 == 1;

    var p5 := FastModularExponentiation(1000, 1000, 1);
    assert p5 == 0;
}
