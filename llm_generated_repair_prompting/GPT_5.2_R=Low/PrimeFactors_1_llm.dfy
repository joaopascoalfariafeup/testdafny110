// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

ghost function Product(s: seq<nat>): nat
{
  if |s| == 0 then 1 else Product(s[..|s|-1]) * s[|s|-1]
}

ghost predicate Nondecreasing(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate IsPrime(p: nat)
{
  p >= 2 && (forall k :: 2 <= k < p ==> p % k != 0)
}

ghost predicate NoDivisorsLessThan(m: nat, d: nat)
{
  forall k :: 2 <= k < d ==> m % k != 0
}

lemma SmallestDivisorIsPrime(m: nat, d: nat)
  requires m > 1
  requires d >= 2
  requires m % d == 0
  requires NoDivisorsLessThan(m, d)
  ensures IsPrime(d)
{
}

lemma MinimalDivisorQuotientAtLeastDiv(m: nat, d: nat)
  requires m > 1
  requires d >= 2
  requires m % d == 0
  requires NoDivisorsLessThan(m, d)
  ensures m == d ==> m / d == 1
  ensures m != d ==> m / d >= d
{
}

method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures Product(f) == n
  ensures Nondecreasing(f)
  ensures forall i :: 0 <= i < |f| ==> IsPrime(f[i])
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant rem >= 1
      invariant 2 <= div
      invariant Product(f) * rem == n
      invariant Nondecreasing(f)
      invariant forall i :: 0 <= i < |f| ==> IsPrime(f[i])
      invariant forall i :: 0 <= i < |f| ==> f[i] <= div
      invariant NoDivisorsLessThan(rem, div)
      invariant div <= rem
      decreases rem, rem - div
    {
        if rem % div == 0 {
            SmallestDivisorIsPrime(rem, div);
            if |f| > 0 {
              assert f[|f|-1] <= div;
            }
            f := f + [div]; 
            MinimalDivisorQuotientAtLeastDiv(rem, div);
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
