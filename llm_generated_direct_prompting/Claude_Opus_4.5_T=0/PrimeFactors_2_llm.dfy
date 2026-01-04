// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

ghost function Product(s: seq<nat>): nat {
    if |s| == 0 then 1 else s[|s|-1] * Product(s[..|s|-1])
}

ghost predicate IsPrime(p: nat) {
    p >= 2 && forall d :: 2 <= d < p ==> p % d != 0
}

ghost predicate AllPrime(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> IsPrime(s[i])
}

ghost predicate NonDescending(s: seq<nat>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate AllFactorsLessThan(n: nat, d: nat) {
    forall p :: 2 <= p < d ==> n % p != 0
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
        invariant 2 <= div
        invariant rem >= 1
        invariant Product(f) * rem == n
        invariant AllPrime(f)
        invariant NonDescending(f)
        invariant AllFactorsLessThan(rem, div)
        invariant |f| > 0 ==> f[|f|-1] <= div
        decreases rem, n - div + 1
    {
        if rem % div == 0 {
            assert IsPrime(div) by {
                if !IsPrime(div) {
                    var d :| 2 <= d < div && div % d == 0;
                    assert rem % d == 0;
                    assert false;
                }
            }
            f := f + [div]; 
            rem := rem / div;
        }
        else {
            div := div + 1;
        }
    }
}





















// ==================== TEST CODE ====================

method {:fuel Product, 4} TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
