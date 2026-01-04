// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.

predicate Divides(a: nat, b: nat)
{
  a > 0 && b % a == 0
}

predicate IsPrime(p: nat)
{
  p >= 2 && (forall d: nat :: 2 <= d < p ==> p % d != 0)
}

predicate NonDecreasing(s: seq<nat>)
{
  forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Product(s: seq<nat>): nat
{
  if |s| == 0 then 1 else s[|s|-1] * Product(s[..|s|-1])
}

lemma DividesTrans(d: nat, a: nat, b: nat)
  requires Divides(d, a)
  requires Divides(a, b)
  ensures Divides(d, b)
{
  var q1: nat := a / d;
  var q2: nat := b / a;
  assert a == d * q1;
  assert b == a * q2;
  calc {
    b;
    == { }
    (d * q1) * q2;
    == { }
    d * (q1 * q2);
  }
}

lemma PrimeFromNoSmallerDivisors(rem: nat, div: nat)
  requires div >= 2
  requires div <= rem
  requires rem % div == 0
  requires forall k: nat :: 2 <= k < div ==> rem % k != 0
  ensures IsPrime(div)
{
  assert div >= 2;
  assert forall d: nat :: 2 <= d < div ==> div % d != 0 by {
    forall d: nat | 2 <= d < div
      ensures div % d != 0
    {
      if div % d == 0 {
        assert Divides(d, div);
        assert Divides(div, rem);
        assert Divides(d, rem) by { DividesTrans(d, div, rem); }
        assert rem % d == 0;
        assert false;
      }
    }
  }
}

method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures Product(f) == n
  ensures NonDecreasing(f)
  ensures forall i: int :: 0 <= i < |f| ==> IsPrime(f[i])
  ensures forall i: int :: 0 <= i < |f| ==> f[i] >= 2
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant rem >= 1
      invariant 2 <= div <= rem
      invariant n == rem * Product(f)
      invariant NonDecreasing(f)
      invariant forall i: int :: 0 <= i < |f| ==> IsPrime(f[i])
      invariant forall i: int :: 0 <= i < |f| ==> f[i] >= 2
      invariant |f| == 0 || f[|f|-1] <= div
      invariant forall k: nat :: 2 <= k < div ==> rem % k != 0
      decreases rem, rem - div
    {
        if rem % div == 0 {
            assert IsPrime(div) by { PrimeFromNoSmallerDivisors(rem, div); }

            f := f + [div]; 
            rem := rem / div;

            assert n == rem * Product(f);

            assert NonDecreasing(f);
            assert forall i: int :: 0 <= i < |f| ==> IsPrime(f[i]);
            assert forall i: int :: 0 <= i < |f| ==> f[i] >= 2;

            assert forall k: nat :: 2 <= k < div ==> rem % k != 0 by {
              forall k: nat | 2 <= k < div
                ensures rem % k != 0
              {
                if rem % k == 0 {
                  assert Divides(k, rem);
                  assert Divides(div, rem * div);
                  assert Divides(k, rem * div) by { DividesTrans(k, rem, rem * div); }
                  assert (rem * div) % k == 0;
                  assert false;
                }
              }
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
