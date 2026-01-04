// Ghost function: product of a sequence of natural numbers
ghost function product(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 1 else product(s[..|s|-1]) * s[|s|-1]
}

// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures |f| > 0
  ensures forall i :: 0 <= i < |f| ==> 2 <= f[i]
  ensures forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j]
  ensures product(f) == n
{
    f  := [];
    var rem := n;
    var div := 2;

    while rem > 1
      invariant 1 <= rem <= n
      invariant 2 <= div
      invariant forall i :: 0 <= i < |f| ==> 2 <= f[i]
      invariant forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j]
      invariant product(f) * rem == n
      decreases rem
    {
        if rem % div == 0 {
            // record old rem for the local proof (avoid 'old', which is for pre-state)
            var rem0 := rem;
            f := f + [div];
            rem := rem / div;

            // facts needed for termination/decrease and arithmetic
            assert rem0 >= 2; // because rem>1 and nat
            assert div >= 2;
            assert div <= rem0; // since div divides rem0 and div>=2
            assert rem < rem0;  // dividing by a number >=2 strictly decreases
        }
        else {
            div := div + 1;
        }
    }

    // From invariant product(f) * rem == n and rem==1 at loop exit
    assert rem == 1;
    assert product(f) == n;

    // n>1 implies there is at least one prime factor, hence f nonempty
    // (this follows from product(f)=n and product([])=1)
    if |f| == 0 {
      assert product(f) == 1;
      assert n == 1;
    }
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);
    // help the verifier with a concrete arithmetic fact about the result
    assert product(f1) == 12;
    assert f1 == [2, 2, 3];
}
