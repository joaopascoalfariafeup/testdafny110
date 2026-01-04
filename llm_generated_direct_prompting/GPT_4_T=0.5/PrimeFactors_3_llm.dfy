// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
    requires n > 1
    ensures forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i + 1]
    ensures forall i :: 0 <= i < |f| ==> 2 <= f[i] <= n
    ensures n == mult(f) && isPrimeFactors(f)
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
        invariant 2 <= div <= n + 1
        invariant rem >= 1
        invariant n == rem * mult(f)
        invariant isPrimeFactors(f)
        invariant forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i + 1]
        invariant forall i :: 0 <= i < |f| ==> 2 <= f[i] <= n
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

ghost function mult(f: seq<nat>): nat
    decreases |f|
{
    if |f| == 0 then 1 else f[0] * mult(f[1..])
}

ghost function isPrimeFactors(f: seq<nat>): bool
    decreases |f|
{
    if |f| == 0 then true 
    else if |f| == 1 then isPrime(f[0]) 
    else isPrime(f[0]) && f[0] <= f[1] && isPrimeFactors(f[1..])
}

ghost function isPrime(n: nat): bool
{
    if n < 2 then false 
    else if n == 2 then true 
    else if n % 2 == 0 then false 
    else forall k :: 1 <= k <= (n - 1) / 2 ==> n % (2 * k + 1) != 0
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
