// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures |f| > 0
  ensures forall i :: 0 <= i < |f| ==> 2 <= f[i]
  ensures forall i :: 0 <= i < |f| ==> IsPrime(f[i])
  ensures Product(f) == n
  ensures forall i :: 0 <= i < |f|-1 ==> f[i] <= f[i+1]
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant 1 <= rem <= n
      invariant div >= 2
      invariant forall i :: 0 <= i < |f| ==> 2 <= f[i]
      invariant forall i :: 0 <= i < |f| ==> IsPrime(f[i])
      invariant Product(f) * rem == n
      invariant forall i :: 0 <= i < |f|-1 ==> f[i] <= f[i+1]
      invariant forall p :: 2 <= p < div && IsPrime(p) ==> rem % p != 0
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

function Product(s: seq<nat>): nat {
  if |s| == 0 then 1 else s[0] * Product(s[1..])
}

predicate IsPrime(p: nat) {
  p >= 2 && forall d :: 2 <= d < p ==> p % d != 0
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
