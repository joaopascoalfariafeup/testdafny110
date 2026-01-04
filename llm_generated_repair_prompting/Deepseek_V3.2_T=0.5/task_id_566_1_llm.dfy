
// Computes the sum of the decimal digits of a natural number n.
method CalcSumOfDigits(n: nat) returns (sum: nat)
  ensures sum == SumOfDigitsSeq(NumberToSeq(n))
{
    sum := 0; // partial sum
    var num : nat := n; // remaining number
    while num > 0           
      invariant sum + SumOfDigitsSeq(NumberToSeq(num)) == SumOfDigitsSeq(NumberToSeq(n))
      invariant num >= 0
    {
        sum := sum + num % 10;
        num := num / 10;
    }
}

ghost function SumOfDigitsSeq(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 0 else s[|s|-1] + SumOfDigitsSeq(s[..|s|-1])
}

ghost function NumberToSeq(n: nat): seq<nat>
  decreases n
{
  if n == 0 then [] else [n % 10] + NumberToSeq(n / 10)
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
