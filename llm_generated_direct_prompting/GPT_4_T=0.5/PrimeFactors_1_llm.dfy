// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
    requires n > 1
    ensures (forall i :: 0 <= i < |f|-1 ==> f[i] <= f[i+1]) // The prime factors are in non-descending order
    ensures (forall p :: p in f ==> IsPrime(p)) // All elements in the sequence are prime
    ensures Product(f) == n // The product of all elements in the sequence is equal to the input number
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1
        invariant 2 <= div <= n+1
        invariant Product(f) * rem == n
        invariant (forall i :: 0 <= i < |f|-1 ==> f[i] <= f[i+1])
        invariant (forall p :: p in f ==> IsPrime(p))
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

// Auxiliary function to determine if a number is prime
function IsPrime(n: nat): bool
    requires n >= 2
{
    (forall i :: 2 <= i < n ==> n % i != 0)
}

// Auxiliary function to compute the product of a sequence of natural numbers
function Product(s: seq<nat>): nat
{
    if |s| == 0 then 1 else s[0] * Product(s[1..])
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
