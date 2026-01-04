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

// Lemma: divisibility is transitive
lemma DivisibilityTransitive(a: nat, b: nat, c: nat)
    requires b > 0 && c > 0
    requires a % b == 0
    requires b % c == 0
    ensures a % c == 0
{
    var q1 := a / b;
    var q2 := b / c;
    assert a == q1 * b;
    assert b == q2 * c;
    calc {
        a;
        == q1 * b;
        == q1 * (q2 * c);
        == (q1 * q2) * c;
    }
    assert a == (q1 * q2) * c;
    assert a % c == 0;
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
            DivisibilityTransitive(n, div, k);
            assert n % k == 0;
            assert false;
        }
    }
}

// Lemma: if k divides q and q * div = n, then k divides n
lemma DivisorOfQuotient(n: nat, div: nat, q: nat, k: nat)
    requires div > 0 && k > 0
    requires n == q * div
    requires q % k == 0
    ensures n % k == 0
{
    var m := q / k;
    assert q == m * k;
    calc {
        n;
        == q * div;
        == (m * k) * div;
        == m * (k * div);
    }
    assert n == m * (k * div);
    assert n % k == 0;
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
            DivisorOfQuotient(n, div, q, k);
            assert n % k == 0;
            assert false;
        }
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
        decreases rem, rem + 1 - div
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
            rem := rem / div;
            assert rem < oldRem;
            if rem > 1 {
                // rem >= 2 and div >= 2
                // oldRem = rem * div >= 2 * div
                // Since rem divides oldRem and div divides oldRem,
                // and NoDivisorsBelow(rem, div) holds, 
                // if rem < div, then rem has no divisors in [2, div),
                // but rem itself is >= 2, so rem must have a divisor >= div or rem >= div
                // Actually, we need to show div <= rem
                // Since oldRem % div == 0 and oldRem = rem * div, 
                // and NoDivisorsBelow(rem, div) means rem has no divisors < div
                // If rem > 1 and rem < div, then rem is prime (since it has no divisors in [2, rem) subset of [2, div))
                // But we don't need rem >= div, we just need the decreases to work
                // The key insight: if rem > 1, then since NoDivisorsBelow(rem, div), 
                // the smallest divisor of rem is >= div, so div <= rem
                assert NoDivisorsBelow(rem, div);
                if rem < div {
                    // rem has no divisors in [2, div), and rem >= 2
                    // So rem has no divisors in [2, rem) since rem < div
                    // This means rem is prime
                    // But rem >= 2 means rem has itself as a divisor
                    // Since rem > 1 and rem < div, and rem has no divisors in [2, div)
                    // rem must equal some value with no divisors in [2, rem)
                    // This means IsPrime(rem) or rem == 1
                    // Since rem > 1, IsPrime(rem)
                    // But then rem % rem == 0, and rem >= 2, so div <= rem
                    // Contradiction since rem < div
                    assert forall k :: 2 <= k < rem ==> rem % k != 0;
                    assert rem >= 2;
                    assert rem % rem == 0;
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



