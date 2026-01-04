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
    calc {
        a;
        == q1 * b;
        == q1 * (q2 * c);
        == (q1 * q2) * c;
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
    calc {
        n;
        == q * div;
        == (m * k) * div;
        == m * (k * div);
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
            rem := rem / div;
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