// Checks if a number greater than 1 is prime.
method IsPrime(n: nat) returns (result: bool)
  requires n > 2
  ensures result ==> (forall i: nat :: 2 <= i <= n/2 + 1 ==> n % i != 0)
  ensures !result ==> (exists i: nat :: 2 <= i <= n/2 + 1 && n % i == 0)
{
    for i := 2 to n/2 + 1
      invariant 2 <= i <= n/2 + 2
      invariant forall j: nat :: 2 <= j < i ==> n % j != 0
    {
        if n % i == 0 {
            assert 2 <= i <= n/2 + 1;
            return false;
        }
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
    assert !out2;

    // large prime number
    var out3 := IsPrime(10007);
    assert out3;
}
