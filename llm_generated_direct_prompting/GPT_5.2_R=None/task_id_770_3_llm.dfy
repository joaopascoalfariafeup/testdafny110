// Returns the sum of the fourth power of the first n odd numbers.
method SumOfFourthPowerOfOddNumbers(n: nat) returns (sum: nat)
    ensures sum == (n * (2 * n + 1) * (2 * n + 1) * (3 * n * n + 3 * n - 1)) / 15
{
    sum := 0;
    var i := 1;
    for k := 0 to n
        invariant i == 2 * k + 1
        invariant sum == (k * (2 * k + 1) * (2 * k + 1) * (3 * k * k + 3 * k - 1)) / 15
    {
        sum := sum + i * i * i * i;
        i := i + 2;
    }
}

// Test cases checked statically.
method SumOfFourthPowerOfOddNumbersTest(){
    var out4 := SumOfFourthPowerOfOddNumbers(0);
    assert out4 == 0;

    var out5 := SumOfFourthPowerOfOddNumbers(1);
    assert out5 == 1;

    var out1 := SumOfFourthPowerOfOddNumbers(2);
    assert out1 == 82;

    var out2 := SumOfFourthPowerOfOddNumbers(3);
    assert out2 == 707;
}
