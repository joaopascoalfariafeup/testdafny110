// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

predicate NonDecreasing(s: seq<nat>)
{
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i+1]
}

function Prod(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 1 else Prod(s[..|s|-1]) * s[|s|-1]
}

predicate IsPrime(p: nat)
{
  p >= 2 && (forall k :: 2 <= k < p ==> p % k != 0)
}

lemma ModZeroImpliesMul(a: nat, b: nat)
  requires a > 0
  requires b % a == 0
  ensures b == a * (b / a)
{
}

lemma DividesTransByMod(b: nat, a: nat, k: nat)
  requires a > 0
  requires k > 0
  requires b % a == 0
  requires a % k == 0
  ensures b % k == 0
{
  ModZeroImpliesMul(a, b);
  ModZeroImpliesMul(k, a);
  calc {
    b;
    == { }
    a * (b / a);
    == { }
    (k * (a / k)) * (b / a);
    == { }
    k * ((a / k) * (b / a));
  }
}

lemma SmallestDivisorIsPrime(rem: nat, div: nat)
  requires rem > 1
  requires div >= 2
  requires rem % div == 0
  requires forall d :: 2 <= d < div ==> rem % d != 0
  ensures IsPrime(div)
{
  assert forall k :: 2 <= k < div ==> div % k != 0 by {
    intro k;
    if div % k == 0 {
      DividesTransByMod(rem, div, k);
      assert rem % k == 0;
      assert false;
    }
  }
}

lemma QuotientAtLeastDivOrOne(rem: nat, div: nat)
  requires rem > 1
  requires div >= 2
  requires rem % div == 0
  requires forall d :: 2 <= d < div ==> rem % d != 0
  ensures rem / div == 1 || rem / div >= div
{
  if rem / div != 1 {
    assert rem / div >= 2;
    if rem / div < div {
      assert 2 <= rem / div < div;
      ModZeroImpliesMul(div, rem);
      assert rem == div * (rem / div);
      assert rem % (rem / div) == 0;
      assert forall d :: 2 <= d < div ==> rem % d != 0;
      assert false;
    }
  }
}

method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures Prod(f) == n
  ensures |f| >= 1
  ensures NonDecreasing(f)
  ensures forall i :: 0 <= i < |f| ==> IsPrime(f[i])
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant rem >= 1
      invariant div >= 2
      invariant Prod(f) * rem == n
      invariant NonDecreasing(f)
      invariant forall i :: 0 <= i < |f| ==> IsPrime(f[i])
      invariant forall i :: 0 <= i < |f| ==> f[i] <= div
      invariant forall d :: 2 <= d < div ==> rem % d != 0
      decreases rem, if rem > 1 && div <= rem then rem - div else 0
    {
        if rem % div == 0 {
            SmallestDivisorIsPrime(rem, div);
            assert IsPrime(div);

            f := f + [div]; 

            NonDecreasing(f);
            assert forall i :: 0 <= i < |f| ==> f[i] <= div;

            rem := rem / div;

            if rem > 1 {
              QuotientAtLeastDivOrOne(old(rem), div);
              assert rem >= div;
            }
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
