// Checks if a number greater than 1 is prime.
method IsPrime(n: nat) returns (result: bool)
  requires n > 1
  ensures result ==> (forall k :: 2 <= k < n ==> n % k != 0)
  ensures !result ==> (exists k :: 2 <= k < n && n % k == 0)
{
    result := true;
    for i := 2 to n/2 + 1
      invariant (forall k :: 2 <= k < i ==> n % k != 0)
    {
        if n % i == 0 {
            result := false;
            return;
        }
    }
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
