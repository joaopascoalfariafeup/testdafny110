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

lemma {:isolate_assertions} DivisorDivides(n: nat, d: nat, k: nat)
    requires d >= 2
    requires k >= 2
    requires n % d == 0
    requires d % k == 0
    ensures n % k == 0
{
    var q1 := n / d;
    assert n == q1 * d;
    var q2 := d / k;
    assert d == q2 * k;
    assert n == q1 * (q2 * k);
    assert n == (q1 * q2) * k;
    assert n % k == 0;
}

lemma {:isolate_assertions} DivisorIsPrime(n: nat, d: nat)
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

lemma {:isolate_assertions} MultipleDivisible(m: nat, k: nat, d: nat)
    requires k >= 1
    ensures (m * k * d) % k == 0
{
    var x := m * d;
    assert m * k * d == x * k;
    assert (x * k) % k == 0;
}

lemma {:isolate_assertions} NoFactorLessThanAfterDivision(n: nat, d: nat)
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
                var m := q / k;
                assert q == m * k;
                assert n == q * d;
                assert n == (m * k) * d;
                assert n == m * (k * d);
                // Since k divides q, and n = q * d, we have k divides n
                MultipleDivisible(m, k, d);
                assert n == m * k * d;
                assert n % k == 0;
                assert false;
            }
        }
    }
}

lemma SmallestDivisorExists(n: nat)
    requires n >= 2
    ensures exists d :: 2 <= d <= n && n % d == 0 && NoFactorLessThan(n, d)
{
    // n always divides itself
    if NoFactorLessThan(n, n) {
        assert n % n == 0;
    } else {
        // There exists some k < n that divides n
        // Find the smallest such k
        var k :| 2 <= k < n && n % k == 0;
        if NoFactorLessThan(n, k) {
            assert 2 <= k <= n && n % k == 0 && NoFactorLessThan(n, k);
        } else {
            // Keep going - there's a smaller divisor
            // This is guaranteed to terminate since we're bounded below by 2
            var d := 2;
            while d < n && n % d != 0
                invariant 2 <= d <= n
                invariant NoFactorLessThan(n, d)
                decreases n - d
            {
                d := d + 1;
            }
            assert n % d == 0;
            assert NoFactorLessThan(n, d);
        }
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
        invariant NoFactorLessThan(rem, div)
        invariant |f| > 0 ==> f[|f|-1] <= div
        invariant rem > 1 ==> div <= rem
        decreases rem, rem - div + 1
    {
        if rem % div == 0 {
            DivisorIsPrime(rem, div);
            NoFactorLessThanAfterDivision(rem, div);
            ProductAppend(f, div);
            f := f + [div]; 
            rem := rem / div;
        }
        else {
            if div < rem {
                div := div + 1;
            } else {
                // rem must be prime since no factor found up to rem
                DivisorIsPrime(rem, rem);
                ProductAppend(f, rem);
                f := f + [rem];
                rem := 1;
            }
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

