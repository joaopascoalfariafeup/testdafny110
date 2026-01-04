// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures forall i :: 0 <= i < |f| ==> f[i] > 1
  ensures forall i :: 0 < i < |f| ==> f[i-1] <= f[i]
  ensures n == Product(f)
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant div <= n
      invariant rem * Product(f) == n
      invariant forall i :: 0 < i < |f| ==> f[i-1] <= f[i]
      invariant forall i :: 0 <= i < |f| ==> f[i] > 1
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

// ==================== AUXILIARY CODE ====================

function {:fuel f} Product(f: seq<nat>): nat
  decreases |f|
{
  if |f| == 0 then 1 else f[0] * Product(f[1..])
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
