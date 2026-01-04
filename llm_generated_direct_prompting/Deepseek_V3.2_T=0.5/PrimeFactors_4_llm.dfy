// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures |f| > 0
  ensures forall i :: 0 <= i < |f| ==> 2 <= f[i]
  ensures forall i :: 0 <= i < |f| ==> (forall d :: 2 <= d < f[i] ==> f[i] % d != 0)
  ensures forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j]
  ensures product(f) == n
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant 1 <= rem <= n
      invariant 2 <= div
      invariant forall d :: 2 <= d < div ==> rem % d != 0
      invariant product(f) * rem == n
      invariant forall i :: 0 <= i < |f| ==> 2 <= f[i]
      invariant forall i :: 0 <= i < |f| ==> (forall d :: 2 <= d < f[i] ==> f[i] % d != 0)
      invariant forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j]
      invariant forall i :: 0 <= i < |f| ==> f[i] >= div || (exists k :: 0 <= k < i && f[k] == f[i])
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

function product(s: seq<nat>): nat
{
  if |s| == 0 then 1 else s[|s|-1] * product(s[..|s|-1])
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
