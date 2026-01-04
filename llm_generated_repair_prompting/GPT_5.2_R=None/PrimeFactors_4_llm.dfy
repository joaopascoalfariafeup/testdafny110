// Ghost function: product of a sequence of natural numbers
ghost function product(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 1 else product(s[..|s|-1]) * s[|s|-1]
}

// Helper: all adjacent elements are nondecreasing (easier to maintain than forall i<j)
ghost predicate Nondecreasing(s: seq<nat>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

// Lemma: adjacent-nondecreasing implies globally sorted (the postcondition form)
lemma NondecreasingImpliesSorted(s: seq<nat>)
  ensures Nondecreasing(s) ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j])
{
  if Nondecreasing(s) {
    // Prove by induction on the distance (j - i)
    forall i, j | 0 <= i < j < |s|
      ensures s[i] <= s[j]
    {
      var d := j - i;
      if d == 1 {
        assert 0 <= i < |s|-1;
        assert s[i] <= s[i+1];
      } else {
        // d > 1
        assert j-1 >= i;
        assert 0 <= j-1 < j < |s|;
        // apply IH to (i, j-1)
        assert s[i] <= s[j-1];
        // use adjacent step (j-1, j)
        assert 0 <= j-1 < |s|-1;
        assert s[j-1] <= s[j];
      }
    }
  }
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
      invariant Nondecreasing(f)
      invariant |f| == 0 || f[|f|-1] <= div
      invariant product(f) * rem == n
      decreases rem, n - rem
    {
        if rem % div == 0 {
            var rem0 := rem;
            // keep last factor <= div so appending preserves Nondecreasing
            if |f| > 0 {
              assert f[|f|-1] <= div;
            }

            f := f + [div];
            rem := rem / div;

            // show rem decreases for lexicographic decreases clause
            assert div >= 2;
            // For nat, rem % div == 0 implies rem = (rem/div) * div
            assert rem0 == (rem0 / div) * div;
            assert rem0 / div <= rem0; // basic nat division fact
            assert rem < rem0;  // since rem0 = rem*div and div>=2 and rem0>1, rem0/div < rem0

            // maintain Nondecreasing after append
            assert Nondecreasing(f[..|f|-1]); // previous f
            if |f| >= 2 {
              // new adjacent pair at the end: old_last <= div
              assert f[|f|-2] <= f[|f|-1];
            }

            // maintain last <= div (now last == div)
            assert f[|f|-1] == div;
        }
        else {
            div := div + 1;
            // maintain last factor <= div when div increases
            if |f| > 0 {
              assert f[|f|-1] <= div - 1;
              assert f[|f|-1] <= div;
            }
        }
    }

    assert rem == 1;
    assert product(f) == n;

    // derive sorted postcondition form
    NondecreasingImpliesSorted(f);
    assert forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j];

    // n>1 implies f nonempty: if f empty then product([])=1 contradicts product(f)=n
    if |f| == 0 {
      assert product(f) == 1;
      assert n == 1;
    }
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);
    assert product(f1) == 12;
    // Help the verifier: the only nondecreasing factorization of 12 into factors >= 2 is [2,2,3]
    // (this follows from the algorithm's behavior, but we give concrete derived facts)
    assert forall i :: 0 <= i < |f1| ==> 2 <= f1[i];
    assert forall i, j :: 0 <= i < j < |f1| ==> f1[i] <= f1[j];
    // Since product is 12 and factors are >=2 and sorted, the sequence must be [2,2,3]
    // Case split on length
    if |f1| == 1 {
      assert product(f1) == f1[0];
      assert f1[0] == 12;
      assert false;
    } else if |f1| == 2 {
      assert product(f1) == f1[0] * f1[1];
      // both >=2, sorted, only possibilities for 12 are [2,6] or [3,4]
      if f1[0] == 2 {
        assert f1[1] == 6;
        assert false;
      } else if f1[0] == 3 {
        assert f1[1] == 4;
        assert false;
      } else {
        assert f1[0] >= 4;
        assert f1[0] * f1[1] >= 4 * 4;
        assert false;
      }
    } else {
      // |f1| >= 3
      // smallest factor must be 2, else product too large or not divisible
      assert f1[0] >= 2;
      if f1[0] > 2 {
        assert f1[0] >= 3;
        assert f1[1] >= 3;
        assert f1[2] >= 3;
        assert product(f1) >= 3 * 3 * 3;
        assert false;
      }
      assert f1[0] == 2;
      // strip first factor
      assert product(f1) == product(f1[1..]) * 2;
      assert product(f1[1..]) == 6;
      // Now similarly force f1[1]=2 and f1[2]=3 and length==3
      if |f1| > 3 {
        assert f1[1] >= 2;
        assert f1[2] >= 2;
        assert f1[3] >= 2;
        assert product(f1[1..]) >= 2 * 2 * 2;
        assert false;
      }
      assert |f1| == 3;
      assert product(f1) == f1[0] * f1[1] * f1[2];
      assert 2 * f1[1] * f1[2] == 12;
      assert f1[1] * f1[2] == 6;
      if f1[1] > 2 {
        assert f1[1] >= 3;
        assert f1[2] >= 3;
        assert f1[1] * f1[2] >= 3 * 3;
        assert false;
      }
      assert f1[1] == 2;
      assert f1[2] == 3;
      assert f1 == [2, 2, 3];
    }
}

