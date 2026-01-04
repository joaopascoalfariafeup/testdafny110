// Checks if a number greater than 1 is prime.
predicate PrimeUpToHalf(n: nat)
{
    n >= 2 && (forall d: nat :: 2 <= d <= n/2 ==> n % d != 0)
}

method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result <==> PrimeUpToHalf(n)
{
    for i := 2 to n/2 + 1
        invariant 2 <= i <= n/2 + 1
        invariant forall d: nat :: 2 <= d < i ==> n % d != 0
    {
        if n % i == 0 {
            assert 2 <= i <= n/2;
            assert !PrimeUpToHalf(n);
            return false;
        }
    }
    assert PrimeUpToHalf(n);
    return true;
}

// Test cases checked statically by Dafny (for not very large numbers)
method IsPrimeTest(){    
    // small prime number
    var out1 := IsPrime(13);
    assert out1;
 
    // non-prime number
    var out2 := IsPrime(1010);
    assert !out2;

    // large prime number
    var out3 := IsPrime(10007);
    assert out3;
}
