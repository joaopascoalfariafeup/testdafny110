// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

function Product(s: seq<nat>): nat
{
  if |s| == 0 then 1 else s[|s|-1] * Product(s[..|s|-1])
}

function FindDivisor(n: nat, d: nat): nat
  requires n > 1
  requires 2 <= d <= n
  ensures d <= FindDivisor(n, d) <= n
  ensures n % FindDivisor(n, d) == 0
  ensures forall k :: d <= k < FindDivisor(n, d) ==> n % k != 0
  decreases n - d
{
  if n % d == 0 then d else FindDivisor(n, d + 1)
}

function PrimeFactorsFrom(n: nat, d: nat): seq<nat>
  requires n > 0
  requires 2 <= d <= n || n == 1
  decreases n
{
  if n == 1 then
    []
  else
    var dd := FindDivisor(n, d);
    [dd] + PrimeFactorsFrom(n / dd, dd)
}

function {:fuel 50} PrimeFactorsSpec(n: nat): seq<nat>
  requires n > 1
{
  PrimeFactorsFrom(n, 2)
}

method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures f == PrimeFactorsSpec(n)
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1
      invariant rem > 0
      invariant 2 <= div <= rem
      invariant forall k :: 2 <= k < div ==> rem % k != 0
      invariant f + PrimeFactorsFrom(rem, div) == PrimeFactorsSpec(n)
      decreases rem, rem - div
    {
        if rem % div == 0 {
            assert div == FindDivisor(rem, div);
            f := f + [div];
            rem := rem / div;
        }
        else {
            div := div + 1;
        }
    }
    assert rem == 1;
    assert PrimeFactorsFrom(rem, div) == [];
    assert f == PrimeFactorsSpec(n);
}





















// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
