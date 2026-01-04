// Calculates the sum and average of the first n natural numbers.
function Tri(n: nat): nat
{
    n * (n + 1) / 2
}

lemma TriStep(k: nat)
    ensures Tri(k + 1) == Tri(k) + (k + 1)
{
}

lemma AvgTri(n: nat)
    requires n > 0
    ensures (Tri(n) as real) / (n as real) == (n as real + 1.0) / 2.0
{
}

method SumAndAverage(n: nat) returns (sum: nat, average: real)
    requires n > 0
    ensures sum == Tri(n)
    ensures average == (sum as real) / (n as real)
    ensures average == (n as real + 1.0) / 2.0
{
    sum := 0;
    for i := 1 to n + 1
        invariant 1 <= i <= n + 1
        invariant sum == Tri(i - 1)
    {
        assert Tri(i - 1) + i == Tri(i) by { TriStep(i - 1); };
        sum := sum + i;
    }
    assert sum == Tri(n);
    average := sum as real / n as real;
    assert average == (n as real + 1.0) / 2.0 by { AvgTri(n); };
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

