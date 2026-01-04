// Returns the sum of the fourth power of the first n odd numbers.
ghost function SumFourthPowerOdd(n: nat): nat
{
    if n == 0 then 0
    else 
        var odd := 2 * (n - 1) + 1;
        SumFourthPowerOdd(n - 1) + odd * odd * odd * odd
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
method SumOfFourthPowerOfOddNumbersTest(){
    var out4 := SumOfFourthPowerOfOddNumbers(0);
    assert SumFourthPowerOdd(0) == 0;
    assert out4 == 0;

    var out5 := SumOfFourthPowerOfOddNumbers(1);
    assert SumFourthPowerOdd(1) == SumFourthPowerOdd(0) + 1 * 1 * 1 * 1;
    assert SumFourthPowerOdd(1) == 1;
    assert out5 == 1;

    var out1 := SumOfFourthPowerOfOddNumbers(2);
    assert SumFourthPowerOdd(2) == SumFourthPowerOdd(1) + 3 * 3 * 3 * 3;
    assert 3 * 3 * 3 * 3 == 81;
    assert SumFourthPowerOdd(2) == 1 + 81;
    assert SumFourthPowerOdd(2) == 82;
    assert out1 == 82;

    var out2 := SumOfFourthPowerOfOddNumbers(3);
    assert SumFourthPowerOdd(3) == SumFourthPowerOdd(2) + 5 * 5 * 5 * 5;
    assert 5 * 5 * 5 * 5 == 625;
    assert SumFourthPowerOdd(3) == 82 + 625;
    assert SumFourthPowerOdd(3) == 707;
    assert out2 == 707;
}

