// Recursive definition of the sum of the decimal digits of a natural number n.
ghost function SumOfDigits(n: nat) : (sum: nat) { 
    if n > 0 then SumOfDigits(n / 10) + n % 10 else 0
}

// Computes the sum of the decimal digits of a natural number n.
method CalcSumOfDigits(n: nat) returns (sum: nat)
    ensures sum == SumOfDigits(n)
    requires n >= 0
{
    sum := 0; // partial sum
    var num : nat := n; // remaining number
    while num > 0           
        invariant SumOfDigits(n) == sum + SumOfDigits(num)  
    {
        sum := sum + num % 10;
        num := num / 10;
    }
}

// Test cases checked statically by Dafny.
method SumOfDigitsTest() {
    var s1 := CalcSumOfDigits(0);
    assert s1 == 0;
    var s2 := CalcSumOfDigits(9);
    assert s2 == 9;
    var s3 := CalcSumOfDigits(10);
    assert s3 == 1;
    var s4 := CalcSumOfDigits(99);
    assert s4 == 18;
    var s5 := CalcSumOfDigits(111111111);
    assert s5 == 9;
}