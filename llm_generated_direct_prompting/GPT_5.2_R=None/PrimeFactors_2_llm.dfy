// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures forall i :: 0 <= i < |f| ==> f[i] >= 2
  ensures forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j]
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant rem >= 1
      invariant div >= 2
      invariant forall i :: 0 <= i < |f| ==> f[i] >= 2
      invariant forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j]
      invariant |f| == 0 || div >= f[|f|-1]
      decreases rem
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





















// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
