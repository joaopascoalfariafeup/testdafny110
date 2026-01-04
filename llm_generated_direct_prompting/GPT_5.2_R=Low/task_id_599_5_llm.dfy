// Calculates the sum and average of the first n natural numbers.
method SumAndAverage(n: nat) returns (sum: nat, average: real)
    requires n > 0
    ensures sum as int == n * (n + 1) / 2
    ensures average == sum as real / n as real
    ensures average == (n + 1) as real / 2.0
{
    sum := 0;
    for i := 1 to n + 1
        invariant 1 <= i <= n + 1
        invariant sum as int == i * (i - 1) / 2
    {
        sum := sum + i;
    }
    average := sum as real / n as real;
}

// Test cases chcked statically.
method SumAndAverageTest(){
    // Small n
    var sum1, avg1 := SumAndAverage(10);
    assert sum1 == 55 && avg1 == 5.5;

    // Large n
    var sum4, avg4 := SumAndAverage(100000);
    assert sum4 == 5000050000 && avg4 == 50000.5;

    // Smallest n
    var sum3, avg3 := SumAndAverage(1);
    assert sum3 == 1 && avg3 == 1.0;
}

