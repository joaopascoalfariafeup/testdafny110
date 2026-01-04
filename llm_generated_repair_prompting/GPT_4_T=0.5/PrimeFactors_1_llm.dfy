// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
    requires n > 1
    ensures forall k :: 0 <= k < |f| ==> f[k] > 1
    ensures |f| > 0
    ensures mult(f) == n
    ensures sorted(f)
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
        invariant rem * mult(f) == n
        invariant forall k :: 0 <= k < |f| ==> f[k] > 1
        invariant div > 1
        invariant sorted(f)
    {
        if rem % div == 0 {
            f := f + [div]; 
            rem := rem / div;
        }
        else {
            div := div + 1;
        }
    }
}

// ==================== HELPER FUNCTIONS ====================

function mult(s: seq<nat>): nat
    decreases |s|
{
    if |s| == 0 then 1 else s[0] * mult(s[1..])
}

predicate sorted(s: seq<nat>) {
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
