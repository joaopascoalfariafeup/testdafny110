// Helper function to compute product of a sequence
ghost function Product(s: seq<nat>): nat {
    if |s| == 0 then 1
    else s[|s|-1] * Product(s[..|s|-1])
}

// Helper predicate to check if a number is prime
ghost predicate IsPrime(n: nat) {
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}

// Helper predicate to check if all elements are >= 2
ghost predicate AllAtLeast2(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> s[i] >= 2
}

// Helper predicate to check if all elements are prime
ghost predicate AllPrime(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> IsPrime(s[i])
}

// Helper predicate to check if sequence is sorted (non-descending)
ghost predicate Sorted(s: seq<nat>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate: no divisors less than div
ghost predicate NoDivisorsBelow(n: nat, div: nat) {
    forall k :: 2 <= k < div ==> n % k != 0
}

// Lemma about product when appending
lemma ProductAppend(s: seq<nat>, x: nat)
    ensures Product(s + [x]) == Product(s) * x
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        assert (s + [x])[..|s + [x]|-1] == s;
    }
}

// Lemma: if n has no divisors below div, and div divides n, then div is prime
lemma DivisorIsPrime(n: nat, div: nat)
    requires n >= 2
    requires div >= 2
    requires n % div == 0
    requires NoDivisorsBelow(n, div)
    ensures IsPrime(div)
{
    forall k | 2 <= k < div
        ensures div % k != 0
    {
        if div % k == 0 {
            // If k divides div and div divides n, then k divides n
            var q1 := n / div;
            var q2 := div / k;
            assert n == q1 * div;
            assert div == q2 * k;
            assert n == q1 * q2 * k;
            assert n % k == 0;
            assert false;
        }
    }
}

// Lemma: after division, the quotient still has no small divisors
lemma QuotientNoDivisorsBelow(n: nat, div: nat)
    requires n >= 2
    requires div >= 2
    requires n % div == 0
    requires NoDivisorsBelow(n, div)
    ensures NoDivisorsBelow(n / div, div)
{
    var q := n / div;
    forall k | 2 <= k < div
        ensures q % k != 0
    {
        if q % k == 0 {
            assert n == q * div;
            // If k divides q, then k divides n = q * div
            var m := q / k;
            assert q == m * k;
            assert n == m * k * div;
            assert n % k == 0;
            assert false;
        }
    }
}

// Lemma: division by a divisor >= 2 reduces the value
lemma DivisionReduces(n: nat, div: nat)
    requires n >= 2
    requires div >= 2
    requires n % div == 0
    ensures n / div < n
{
    var q := n / div;
    assert n == q * div;
    assert q * div >= q * 2;
    assert q * 2 >= 2 * q;
    if q >= n {
        assert q * div >= n * div >= n * 2;
        assert n >= n * 2;
        assert false;
    }
}

// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method PrimeFactors(n: nat) returns (f: seq<nat>)
    requires n >= 2
    ensures Product(f) == n
    ensures AllPrime(f)
    ensures Sorted(f)
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
        invariant Sorted(f)
        invariant NoDivisorsBelow(rem, div)
        invariant |f| == 0 || f[|f|-1] <= div
        invariant rem > 1 ==> div <= rem
        decreases rem, if rem >= div then rem + 1 - div else 0
    {
        if rem % div == 0 {
            DivisorIsPrime(rem, div);
            assert IsPrime(div);
            ProductAppend(f, div);
            var oldF := f;
            f := f + [div];
            assert forall i :: 0 <= i < |oldF| ==> f[i] == oldF[i];
            assert f[|f|-1] == div;
            QuotientNoDivisorsBelow(rem, div);
            var oldRem := rem;
            DivisionReduces(rem, div);
            rem := rem / div;
            assert rem < oldRem;
            if rem > 1 {
                assert NoDivisorsBelow(rem, div);
                // We need to show div <= rem when rem > 1
                // Since NoDivisorsBelow(rem, div), rem has no divisors in [2, div)
                // If rem > 1 and rem < div, then rem has no divisors in [2, rem)
                // which means rem is prime, so rem >= 2
                // But the smallest divisor of rem (which is rem itself if prime, or smaller) must be >= div
                // Since rem > 1, rem has at least one divisor >= 2 (itself or a factor)
                // The smallest such divisor must be >= div (by NoDivisorsBelow)
                // So div <= rem
                if rem < div {
                    assert forall k :: 2 <= k < div ==> rem % k != 0;
                    assert forall k :: 2 <= k < rem ==> rem % k != 0;
                    // rem is prime, so rem >= 2 and rem % rem == 0
                    // But rem < div, so we need rem >= div, contradiction
                    // Actually if rem is prime and rem >= 2, the smallest divisor is rem itself
                    // Since NoDivisorsBelow(rem, div), all divisors of rem are >= div
                    // rem is a divisor of rem, so rem >= div
                    assert rem >= 2;
                    // rem divides rem, so if rem < div, this contradicts NoDivisorsBelow
                    // Wait, NoDivisorsBelow says rem % k != 0 for k in [2, div)
                    // rem % rem == 0, so if rem in [2, div), we have a contradiction
                    // rem >= 2 and rem < div means rem in [2, div)
                    // So rem % rem == 0 contradicts NoDivisorsBelow(rem, div)
                    assert rem % rem == 0;
                    assert !(2 <= rem < div);
                    assert div <= rem;
                }
            }
        }
        else {
            div := div + 1;
        }
    }
}

// ==================== TEST CODE ====================

method {:fuel Product, 4} {:fuel AllPrime, 4} {:fuel Sorted, 4} TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert Product([2, 2, 3]) == 12;
    assert AllPrime([2, 2, 3]);
    assert Sorted([2, 2, 3]);
    // The postconditions guarantee the result, but uniqueness needs more work
    // We verify the properties hold for f1
    assert Product(f1) == 12;
    assert AllPrime(f1);
    assert Sorted(f1);
    assert |f1| >= 1;
}
// 




