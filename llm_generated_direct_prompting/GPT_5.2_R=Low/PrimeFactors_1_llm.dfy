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
  p >= 2 && (forall d :: 2 <= d < p ==> p % d != 0)
}

lemma ProductAppend(s: seq<nat>, x: nat)
  ensures Product(s + [x]) == Product(s) * x
{
}

lemma DivisibleTrans(a: nat, b: nat, c: nat)
  requires b > 0 && c > 0
  requires a % b == 0
  requires b % c == 0
  ensures a % c == 0
{
  var k := a / b;
  var m := b / c;
  assert a == b * k;
  assert b == c * m;
  assert a == c * (m * k);
  assert a % c == 0;
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
      invariant div >= 2
      invariant Product(f) * rem == n
      invariant Nondecreasing(f)
      invariant forall i :: 0 <= i < |f| ==> IsPrime(f[i])
      invariant forall i :: 0 <= i < |f| ==> f[i] <= div
      invariant rem > 1 ==> div <= rem
      invariant forall k :: 2 <= k < div ==> rem % k != 0
      decreases rem, rem - div
    {
        if rem % div == 0 {
            assert rem > 1 ==> div <= rem;
            assert div >= 2;
            assert div <= rem;
            assert forall d :: 2 <= d < div ==> div % d != 0 by {
              forall d | 2 <= d < div
                ensures div % d != 0
              {
                if div % d == 0 {
                  DivisibleTrans(rem, div, d);
                  assert rem % d == 0;
                  assert false;
                }
              }
            }
            assert IsPrime(div);

            ProductAppend(f, div);
            f := f + [div]; 
            rem := rem / div;

            assert Product(f) * rem == n;
            assert forall k :: 2 <= k < div ==> rem % k != 0 by {
              forall k | 2 <= k < div
                ensures rem % k != 0
              {
                if rem % k == 0 {
                  // (old rem) = div * rem, so k divides old rem, contradicting invariant
                  assert rem * div == (rem * div);
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
