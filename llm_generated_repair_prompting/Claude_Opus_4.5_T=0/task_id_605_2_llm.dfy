// Checks if a number greater than 1 is prime.
ghost predicate HasDivisorInRange(n: nat, lo: nat, hi: nat)
{
    exists d :: lo <= d < hi && d > 0 && n % d == 0
}

ghost predicate IsPrimeSpec(n: nat)
{
    n > 1 && !HasDivisorInRange(n, 2, n)
}

lemma NoDivisorAboveHalf(n: nat)
    requires n > 2
    ensures forall d :: n/2 + 1 <= d < n ==> n % d != 0
{
    forall d | n/2 + 1 <= d < n
        ensures n % d != 0
    {
        if n % d == 0 {
            var q := n / d;
            assert n == q * d;
            assert q >= 1;
            if q == 1 {
                assert n == d;
                assert d < n;
                assert false;
            } else {
                assert q >= 2;
                assert n >= 2 * d;
                assert d <= n / 2;
                assert d >= n/2 + 1;
                assert false;
            }
        }
    }
}

lemma NoDivisorAboveHalfImpliesNoDivisor(n: nat)
    requires n > 2
    requires !HasDivisorInRange(n, 2, n/2 + 1)
    ensures !HasDivisorInRange(n, 2, n)
{
    NoDivisorAboveHalf(n);
    if HasDivisorInRange(n, 2, n) {
        var d :| 2 <= d < n && d > 0 && n % d == 0;
        if d < n/2 + 1 {
            assert HasDivisorInRange(n, 2, n/2 + 1);
            assert false;
        } else {
            assert n % d != 0;
            assert false;
        }
    }
}

method IsPrime(n: nat) returns (result: bool)
    requires n > 1
    ensures result == IsPrimeSpec(n)
{
    for i := 2 to n/2 + 1
        invariant !HasDivisorInRange(n, 2, i)
    {
        if n % i == 0 {
            assert i > 0 && 2 <= i < n && n % i == 0;
            assert HasDivisorInRange(n, 2, n);
            return false;
        }
    }
    assert !HasDivisorInRange(n, 2, n/2 + 1);
    if n > 2 {
        NoDivisorAboveHalfImpliesNoDivisor(n);
    }
    return true;
}

// Test cases checked statically by Dafny (for not very large numbers)
method IsPrimeTest(){    
    // small prime number
    var out1 := IsPrime(13);
    assert out1;
 
    // non-prime number
    var out2 := IsPrime(1010);
    assert 1010 % 2 == 0;
    assert HasDivisorInRange(1010, 2, 1010);
    assert !IsPrimeSpec(1010);
    assert !out2;

    // large prime number
    var out3 := IsPrime(10007);
    assert out3;
}

