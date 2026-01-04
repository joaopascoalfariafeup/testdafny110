// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

ghost predicate IsPrime(n: nat)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}

ghost function Product(s: seq<nat>): nat
{
    if |s| == 0 then 1 else s[|s|-1] * Product(s[..|s|-1])
}

ghost predicate AllPrime(s: seq<nat>)
{
    forall i :: 0 <= i < |s| ==> IsPrime(s[i])
}

ghost predicate NonDescending(s: seq<nat>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate AllAtLeast(s: seq<nat>, min: nat)
{
    forall i :: 0 <= i < |s| ==> s[i] >= min
}

ghost predicate NoFactorsBelow(n: nat, d: nat)
{
    forall k :: 2 <= k < d ==> n % k != 0
}

lemma ProductAppend(s: seq<nat>, x: nat)
    ensures Product(s + [x]) == Product(s) * x
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        assert (s + [x])[..|s + [x]| - 1] == s;
    }
}

lemma AllPrimeAppend(s: seq<nat>, x: nat)
    requires AllPrime(s)
    requires IsPrime(x)
    ensures AllPrime(s + [x])
{
}

lemma NonDescendingAppend(s: seq<nat>, x: nat)
    requires NonDescending(s)
    requires AllAtLeast(s, 2)
    requires |s| > 0 ==> s[|s|-1] <= x
    ensures NonDescending(s + [x])
{
}

lemma AllAtLeastAppend(s: seq<nat>, x: nat, min: nat)
    requires AllAtLeast(s, min)
    requires x >= min
    ensures AllAtLeast(s + [x], min)
{
}

lemma SmallestDivisorIsPrime(n: nat, d: nat)
    requires n >= 2
    requires d >= 2
    requires n % d == 0
    requires NoFactorsBelow(n, d)
    ensures IsPrime(d)
{
    if !IsPrime(d) {
        var k :| 2 <= k < d && d % k == 0;
        assert n % k == 0;
        assert false;
    }
}

method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
    requires n >= 2
    ensures Product(f) == n
    ensures AllPrime(f)
    ensures NonDescending(f)
    ensures |f| >= 1
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
        invariant 2 <= div
        invariant rem >= 1
        invariant Product(f) * rem == n
        invariant AllPrime(f)
        invariant NonDescending(f)
        invariant AllAtLeast(f, 2)
        invariant |f| > 0 ==> f[|f|-1] <= div
        invariant NoFactorsBelow(rem, div)
    {
        if rem % div == 0 {
            SmallestDivisorIsPrime(rem, div);
            ProductAppend(f, div);
            AllPrimeAppend(f, div);
            NonDescendingAppend(f, div);
            AllAtLeastAppend(f, div, 2);
            f := f + [div]; 
            rem := rem / div;
        }
        else {
            div := div + 1;
        }
    }
}





















// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
