// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

function {:fuel 50} FactorsFrom(rem: nat, div: nat): seq<nat>
  requires rem >= 1
  requires rem == 1 || 2 <= div <= rem
  decreases rem, (if rem == 1 then 0 else rem - div)
{
  if rem == 1 then
    []
  else if rem % div == 0 then
    [div] + FactorsFrom(rem / div, div)
  else
    FactorsFrom(rem, div + 1)
}

method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures f == FactorsFrom(n, 2)
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant rem >= 1
      invariant rem == 1 || 2 <= div <= rem
      invariant f + FactorsFrom(rem, div) == FactorsFrom(n, 2)
      decreases rem, (if rem == 1 then 0 else rem - div)
    {
        if rem % div == 0 {
            assert FactorsFrom(rem, div) == [div] + FactorsFrom(rem / div, div);
            f := f + [div]; 
            rem := rem / div;
            assert f + FactorsFrom(rem, div) == FactorsFrom(n, 2);
        }
        else {
            assert div < rem;
            assert FactorsFrom(rem, div) == FactorsFrom(rem, div + 1);
            div := div + 1;
            assert f + FactorsFrom(rem, div) == FactorsFrom(n, 2);
        }
    }
    assert FactorsFrom(rem, div) == [];
}





















// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
