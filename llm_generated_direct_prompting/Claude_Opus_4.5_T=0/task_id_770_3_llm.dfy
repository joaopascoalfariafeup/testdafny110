// Returns the sum of the fourth power of the first n odd numbers.
ghost function SumFourthPowerOdd(n: nat): nat
{
    if n == 0 then 0
    else 
        var oddNum := 2 * (n - 1) + 1;
        SumFourthPowerOdd(n - 1) + oddNum * oddNum * oddNum * oddNum
}

method SumOfFourthPowerOfOddNumbers(n: nat) returns (sum: nat)
    ensures sum == SumFourthPowerOdd(n)
{
    sum := 0;
    var i := 1;
    for k := 0 to n
        invariant i == 2 * k + 1
        invariant sum == SumFourthPowerOdd(k)
    {
        sum := sum + i * i * i * i;
        i := i + 2;
    }
}

// Test cases checked statically.
method {:fuel SumFourthPowerOdd, 4} SumOfFourthPowerOfOddNumbersTest(){
    var out4 := SumOfFourthPowerOfOddNumbers(0);
    assert out4 == 0;

    var out5 := SumOfFourthPowerOfOddNumbers(1);
    assert out5 == 1;

    var out1 := SumOfFourthPowerOfOddNumbers(2);
    assert out1 == 82;

    var out2 := SumOfFourthPowerOfOddNumbers(3);
    assert out2 == 707;
}
