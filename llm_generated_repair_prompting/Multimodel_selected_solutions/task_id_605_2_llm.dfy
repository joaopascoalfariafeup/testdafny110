// Checks if a number greater than 1 is prime.
ghost predicate HasDivisorInRange(n: nat, lo: nat, hi: nat)
{
    exists d :: lo <= d < hi && d > 0 && n % d == 0
}

ghost predicate IsPrimeSpec(n: nat)
{
    n > 1 && !HasDivisorInRange(n, 2, n)
}

method IsPrime(n: nat) returns (result: bool)
    requires n > 1
    ensures result == IsPrimeSpec(n)
{
    for i := 2 to n/2 + 1
        invariant !HasDivisorInRange(n, 2, i)
    {
        if n % i == 0 {
            assert HasDivisorInRange(n, 2, n/2 + 1);
            assert HasDivisorInRange(n, 2, n);
            return false;
        }
    }
    assert !HasDivisorInRange(n, 2, n/2 + 1);
    if n == 2 {
        return true;
    }
    forall d | n/2 + 1 <= d < n
        ensures n % d != 0
    {
        if n % d == 0 {
            var q := n / d;
            assert q * d == n;
            assert q >= 2;
            assert q <= n / 2;
            assert HasDivisorInRange(n, 2, n/2 + 1);
        }
    }
    assert !HasDivisorInRange(n, n/2 + 1, n);
    assert !HasDivisorInRange(n, 2, n);
    return true;
}

// Test cases checked statically by Dafny (for not very large numbers)
method IsPrimeTest(){    
    // small prime number
    var out1 := IsPrime(13);
    assert out1;
 
    // non-prime number
    var out2 := IsPrime(1010);
    // 1010 = 2 * 505, so 2 is a divisor
    assert 1010 % 2 == 0;
    assert 2 >= 2 && 2 < 1010 && 2 > 0 && 1010 % 2 == 0;
    assert HasDivisorInRange(1010, 2, 1010);
    assert !IsPrimeSpec(1010);
    assert !out2;

    // large prime number
    var out3 := IsPrime(10007);
    assert out3;
}

