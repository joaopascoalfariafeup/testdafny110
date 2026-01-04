// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

ghost function Product(s: seq<nat>): nat {
    if |s| == 0 then 1 else s[|s|-1] * Product(s[..|s|-1])
}

ghost predicate IsPrime(n: nat) {
    n >= 2 && forall d :: 2 <= d < n ==> n % d != 0
}

ghost predicate AllPrime(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> IsPrime(s[i])
}

ghost predicate NonDescending(s: seq<nat>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate NoFactorLessThan(n: nat, d: nat) {
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

lemma DivisorDivides(n: nat, d: nat, k: nat)
    requires d >= 2
    requires k >= 2
    requires n % d == 0
    requires d % k == 0
    ensures n % k == 0
{
    var q1 := n / d;
    var q2 := d / k;
    assert d == q2 * k;
    assert n == q1 * d;
    assert n == q1 * q2 * k;
}

lemma DivisorIsPrime(n: nat, d: nat)
    requires n >= 2
    requires d >= 2
    requires n % d == 0
    requires NoFactorLessThan(n, d)
    ensures IsPrime(d)
{
    forall k | 2 <= k < d
        ensures d % k != 0
    {
        if d % k == 0 {
            DivisorDivides(n, d, k);
            assert n % k == 0;
            assert false;
        }
    }
}

lemma NoFactorLessThanAfterDivision(n: nat, d: nat)
    requires n >= 2
    requires d >= 2
    requires n % d == 0
    requires NoFactorLessThan(n, d)
    ensures NoFactorLessThan(n / d, d)
{
    var q := n / d;
    if q < 2 {
        // trivially true
    } else {
        forall k | 2 <= k < d
            ensures q % k != 0
        {
            if q % k == 0 {
                assert n == q * d;
                DivisorDivides(n, q, k);
                assert n % k == 0;
                assert false;
            }
        }
    }
}

lemma DivisorDividesProduct(q: nat, d: nat, k: nat)
    requires d >= 1
    requires k >= 2
    requires q % k == 0
    ensures (q * d) % k == 0
{
    var m := q / k;
    assert q == m * k;
    assert q * d == m * k * d;
    assert (q * d) % k == 0;
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
        invariant NoFactorLessThan(rem, div)
        invariant |f| > 0 ==> f[|f|-1] <= div
        invariant div <= rem || rem == 1
        decreases rem, if rem > 1 && div <= rem then rem - div + 1 else 0
    {
        if rem % div == 0 {
            DivisorIsPrime(rem, div);
            NoFactorLessThanAfterDivision(rem, div);
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

lemma {:fuel Product, 4} ProductExample()
    ensures Product([2, 2, 3]) == 12
{
    assert [2, 2, 3][..2] == [2, 2];
    assert [2, 2][..1] == [2];
    assert [2][..0] == [];
}

lemma {:fuel AllPrime, 4} AllPrimeExample()
    ensures AllPrime([2, 2, 3])
{
}

lemma {:fuel NonDescending, 4} NonDescendingExample()
    ensures NonDescending([2, 2, 3])
{
}

method {:fuel Product, 4} {:fuel AllPrime, 4} {:fuel NonDescending, 4} TestPrimeFactors() {
    var f1 := PrimeFactors(12);
    ProductExample();
    AllPrimeExample();
    NonDescendingExample();
    assert Product([2, 2, 3]) == 12;
    assert AllPrime([2, 2, 3]);
    assert NonDescending([2, 2, 3]);
    // The postconditions guarantee Product(f1) == 12, AllPrime(f1), NonDescending(f1)
    // but we cannot assert the exact sequence without a uniqueness lemma
    assert Product(f1) == 12;
    assert AllPrime(f1);
    assert NonDescending(f1);
}
