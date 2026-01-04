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

ghost predicate NoFactorLessThan(n: nat, d: nat)
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

lemma DivisorIsPrimeOrHasSmallerFactor(n: nat, d: nat)
    requires n >= 2
    requires d >= 2
    requires n % d == 0
    requires NoFactorLessThan(n, d)
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
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
        invariant 1 <= rem <= n
        invariant 2 <= div
        invariant Product(f) * rem == n
        invariant AllPrime(f)
        invariant NonDescending(f)
        invariant |f| > 0 ==> f[|f|-1] <= div
        invariant NoFactorLessThan(rem, div)
        decreases rem, n - div + 1
    {
        if rem % div == 0 {
            DivisorIsPrimeOrHasSmallerFactor(rem, div);
            ProductAppend(f, div);
            f := f + [div]; 
            rem := rem / div;
        }
        else {
            div := div + 1;
        }
    }
}





















// ==================== TEST CODE ====================

method {:fuel Product, 4} {:fuel AllPrime, 4} {:fuel NonDescending, 4} TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
