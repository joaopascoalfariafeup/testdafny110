// Checks if a number greater than 1 is prime.
method IsPrime(n: nat) returns (result: bool)
  requires n >= 3
  ensures result ==> (forall d :: 2 <= d <= n/2 + 1 ==> n % d != 0)
  ensures !result ==> (exists d :: 2 <= d <= n/2 + 1 && n % d == 0)
{
    for i := 2 to n/2 + 1
      invariant 2 <= i <= n/2 + 2
      invariant forall k :: 2 <= k < i ==> n % k != 0
    {
        if n % i == 0 {
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
