// Returns the sum of the fourth power of the first n odd numbers.
method SumOfFourthPowerOfOddNumbers(n: nat) returns (sum: nat)
  ensures sum == n * (16 * n * n * n * n - 16 * n * n * n + 6 * n * n) / 15 + 1
{
    sum := 1;
    var i := 1;
    for k := 0 to n
      invariant sum == k * (16 * k * k * k * k - 16 * k * k * k + 6 * k * k) / 15 + 1
      invariant i == 2 * k + 1
    {
        sum := sum + i * i * i * i;
        i := i + 2;
    }
}

// Test cases checked statically.
method SumOfFourthPowerOfOddNumbersTest(){
    var out4 := SumOfFourthPowerOfOddNumbers(0);
    assert out4 == 1;

    var out5 := SumOfFourthPowerOfOddNumbers(1);
    assert out5 == 1;

    var out1 := SumOfFourthPowerOfOddNumbers(2);
    assert out1 == 83;

    var out2 := SumOfFourthPowerOfOddNumbers(3);
    assert out2 == 707;
}
