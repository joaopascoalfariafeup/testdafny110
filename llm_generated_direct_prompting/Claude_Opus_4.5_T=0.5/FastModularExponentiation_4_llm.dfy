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

// Lemma for the loop invariant relationship
lemma PowerDecomposition(mx: nat, mn: nat, p: nat)
    ensures p * Power(mx, mn) == p * Power(mx, mn)
{
}

// Lemma: if mn is odd, Power(mx, mn) == mx * Power(mx, mn - 1)
lemma PowerOdd(mx: nat, mn: nat)
    requires mn > 0
    ensures Power(mx, mn) == mx * Power(mx, mn - 1)
{
}

// Lemma: Power(mx * mx, mn / 2) == Power(mx, 2 * (mn / 2))
lemma PowerSquare(mx: nat, mn: nat)
    ensures Power(mx * mx, mn / 2) == Power(mx, 2 * (mn / 2))
{
    calc {
        Power(mx * mx, mn / 2);
        == { PowerMultiplication(mx, 2, mn / 2); }
           Power(Power(mx, 2), mn / 2);
        == Power(mx, 2 * (mn / 2));
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
        invariant p * Power(mx, mn) == Power(x, n)
    {
        if mn % 2 == 1 {
            p := p * mx;
        } 
        PowerSquare(mx, mn);
        mx := mx * mx;
        mn := mn / 2;
    }
}

// Lemma for modular arithmetic: (a * b) % m == ((a % m) * (b % m)) % m
lemma ModMultiplication(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

// Lemma: Power(x, n) % m == result from modular exponentiation
lemma ModPower(x: nat, n: nat, m: nat)
    requires m > 1
    ensures Power(x, n) % m == Power(x % m, n) % m
{
    if n == 0 {
    } else {
        calc {
            Power(x, n) % m;
            == (x * Power(x, n - 1)) % m;
            == { ModMultiplication(x, Power(x, n - 1), m); }
               ((x % m) * (Power(x, n - 1) % m)) % m;
            == { ModPower(x, n - 1, m); }
               ((x % m) * (Power(x % m, n - 1) % m)) % m;
            == { ModMultiplication(x % m, Power(x % m, n - 1), m); }
               ((x % m) * Power(x % m, n - 1)) % m;
            == Power(x % m, n) % m;
        }
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

    while mn > 0 
        invariant (p2 * Power(mx2, mn)) % m == Power(x % m, n) % m
        invariant p2 < m
        invariant mx2 < m
    {
        ghost var old_mn := mn;
        ghost var old_mx2 := mx2;
        ghost var old_p2 := p2;
        
        if mn % 2 == 1 {
            assert Power(mx2, mn) == mx2 * Power(mx2, mn - 1);
            p2 := (p2 * mx2) % m;
        } 
        mn := mn / 2;
        PowerSquare(old_mx2, old_mn);
        mx2 := (mx2 * mx2) % m;
    }
    
    ModPower(x, n, m);
    return p2;
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
