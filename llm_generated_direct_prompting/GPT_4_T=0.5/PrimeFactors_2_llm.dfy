// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i+1]  // factors are in non-descending order
  ensures mult(f) == n  // the multiplication of all factors equals the original number
{
    f  := [];
    var rem := n;
    var div := 2;

    while rem > 1 
      invariant div > 1
      invariant rem >= 1
      invariant mult(f) * rem == n
      invariant forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i+1]
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

// Auxiliary function to calculate the multiplication of all elements in a sequence
function {:fuel n} mult(s: seq<nat>): nat
{
    if |s| == 0 then 1 else s[0]*mult(s[1..])
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
