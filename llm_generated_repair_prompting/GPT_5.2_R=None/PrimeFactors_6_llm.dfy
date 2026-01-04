// Ghost function: product of a sequence of natural numbers
ghost function {:fuel 5} product(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 1 else product(s[..|s|-1]) * s[|s|-1]
}

lemma ProductAppend(s: seq<nat>, x: nat)
  ensures product(s + [x]) == product(s) * x
{
  // unfold product on s+[x]
  assert (s + [x])[..|(s + [x])|-1] == s;
  assert (s + [x])[|(s + [x])|-1] == x;
}

lemma ProductDropFirst(s: seq<nat>)
  requires |s| > 0
  ensures product(s) == s[0] * product(s[1..])
{
  // Use a simple calculation with "append last" and avoid heavy induction
  if |s| == 1 {
    assert s[1..] == [];
  } else {
    var t := s[1..];
    // s == [s[0]] + t
    assert s == [s[0]] + t;

    // product([s[0]] + t) = product(t + [s[0]])? No, use product definition via last:
    // Rewrite [s[0]]+t as ( ([s[0]]+t)[..|s|-1] ) + [last]
    assert s[..|s|-1] == [s[0]] + t[..|t|-1];
    assert s[|s|-1] == t[|t|-1];

    calc {
      product(s);
      == { }
      product(s[..|s|-1]) * s[|s|-1];
      == {
        // unfold s[..|s|-1] and last
        assert s[..|s|-1] == [s[0]] + t[..|t|-1];
        assert s[|s|-1] == t[|t|-1];
      }
      product([s[0]] + t[..|t|-1]) * t[|t|-1];
    }

    // Now show: product([s0] + t[..|t|-1]) == s0 * product(t[..|t|-1])
    // by unfolding product on ([s0] + prefix)
    var u := t[..|t|-1];
    assert [s[0]] + u != [];
    calc {
      product([s[0]] + u);
      == { }
      product(([s[0]] + u)[..|([s[0]] + u)|-1]) * ([s[0]] + u)[|([s[0]] + u)|-1];
      == {
        assert ([s[0]] + u)[..|([s[0]] + u)|-1] == [s[0]] + u[..|u|-1];
        assert ([s[0]] + u)[|([s[0]] + u)|-1] == u[|u|-1];
      }
      product([s[0]] + u[..|u|-1]) * u[|u|-1];
    }

    // Instead of expanding further, just use ProductAppend twice to build product(t) from u
    ProductAppend(u[..|u|], t[|t|-1]);
    assert product(t) == product(u + [t[|t|-1]]); // since t == u + [last]
    assert t == u + [t[|t|-1]];
    assert product(t) == product(u) * t[|t|-1];

    // Also product([s0] + u) = s0 * product(u) (since [s0]+u == u' + [last] form is annoying),
    // so use ProductAppend with empty-start on the left part:
    // product([s0] + u) == product([s0] + u[..|u|]) and then append last repeatedly is expensive.
    // Instead, use product definition on the front by a small auxiliary fact:
    // product([a] + r) == a * product(r), proven by unfolding on (r+[a]) with commutativity? Not available.
    // So do a tiny induction on |t| (which is |s|-1) but only on that tail, which is smaller and fast.

    TailProductPrefix(s[0], t);
    assert product([s[0]] + t) == s[0] * product(t);
  }
}

lemma TailProductPrefix(a: nat, t: seq<nat>)
  ensures product([a] + t) == a * product(t)
  decreases |t|
{
  if |t| == 0 {
    assert [a] + t == [a];
  } else {
    // t == tprefix + [last]
    assert t == t[..|t|-1] + [t[|t|-1]];
    // [a]+t == ([a]+tprefix) + [last]
    assert [a] + t == ([a] + t[..|t|-1]) + [t[|t|-1]];
    ProductAppend([a] + t[..|t|-1], t[|t|-1]);
    ProductAppend(t[..|t|-1], t[|t|-1]);
    TailProductPrefix(a, t[..|t|-1]);
    calc {
      product([a] + t);
      == { assert [a] + t == ([a] + t[..|t|-1]) + [t[|t|-1]]; }
      product(([a] + t[..|t|-1]) + [t[|t|-1]]);
      == { ProductAppend([a] + t[..|t|-1], t[|t|-1]); }
      product([a] + t[..|t|-1]) * t[|t|-1];
      == { TailProductPrefix(a, t[..|t|-1]); }
      (a * product(t[..|t|-1])) * t[|t|-1];
      == { ProductAppend(t[..|t|-1], t[|t|-1]); }
      a * product(t[..|t|-1] + [t[|t|-1]]);
      == { assert t == t[..|t|-1] + [t[|t|-1]]; }
      a * product(t);
    }
  }
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
    // Use a small explicit induction on the distance (j-i)
    forall i, j | 0 <= i < j < |s|
      ensures s[i] <= s[j]
      decreases j - i
    {
      if j == i + 1 {
        assert 0 <= i < |s|-1;
        assert s[i] <= s[i+1];
      } else {
        // apply IH to (i, j-1)
        assert 0 <= i < j-1 < |s|;
        assert s[i] <= s[j-1];
        // adjacent step (j-1, j)
        assert 0 <= j-1 < |s|-1;
        assert s[j-1] <= s[j];
        assert s[i] <= s[j];
      }
    }
  }
}

lemma DivStrictDecreases(rem0: nat, div: nat)
  requires div >= 2
  requires rem0 > 0
  ensures rem0 / div <= rem0
  ensures rem0 > 1 ==> rem0 / div < rem0
{
  assert rem0 / div <= rem0;
  if rem0 > 1 {
    var q := rem0 / div;
    var r := rem0 % div;
    assert rem0 == q * div + r;
    assert r < div;
    if q >= rem0 {
      assert q * div >= rem0 * 2;
      assert rem0 * 2 > rem0;
      assert q * div > rem0;
      assert q * div + r > rem0;
      assert false;
    }
    assert q < rem0;
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
      decreases rem
    {
        if rem % div == 0 {
            var rem0 := rem;

            if |f| > 0 {
              assert f[|f|-1] <= div;
            }

            f := f + [div];
            rem := rem / div;

            assert div >= 2;
            assert rem0 == (rem0 / div) * div; // since rem0 % div == 0

            DivStrictDecreases(rem0, div);
            assert rem0 / div <= rem0;
            if rem0 > 1 {
              assert rem < rem0;
            }

            // maintain Nondecreasing after append
            assert Nondecreasing(f[..|f|-1]);
            if |f| >= 2 {
              assert f[|f|-2] <= f[|f|-1];
            }

            assert f[|f|-1] == div;

            // maintain product(f) * rem == n
            ProductAppend(f[..|f|-1], div);
            assert product(f) == product(f[..|f|-1]) * div;
            assert product(f[..|f|-1]) * rem0 == n;
            assert rem0 == rem * div;
            assert product(f) * rem == n;
        }
        else {
            div := div + 1;
            if |f| > 0 {
              assert f[|f|-1] <= div - 1;
              assert f[|f|-1] <= div;
            }
        }
    }

    assert rem == 1;
    assert product(f) == n;

    NondecreasingImpliesSorted(f);
    assert forall i, j :: 0 <= i < j < |f| ==> f[i] <= f[j];

    if |f| == 0 {
      assert product(f) == 1;
      assert n == 1;
    }
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);
    assert product(f1) == 12;

    assert forall i :: 0 <= i < |f1| ==> 2 <= f1[i];
    assert forall i, j :: 0 <= i < j < |f1| ==> f1[i] <= f1[j];

    if |f1| == 1 {
      assert product(f1) == f1[0];
      assert f1[0] == 12;
      assert false;
    } else if |f1| == 2 {
      assert product(f1) == f1[0] * f1[1];
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
      assert f1[0] >= 2;
      if f1[0] > 2 {
        assert f1[0] >= 3;
        assert f1[1] >= 3;
        assert f1[2] >= 3;
        // enough: each factor >=3 implies product >=27 > 12
        ProductDropFirst(f1);
        assert product(f1) == f1[0] * product(f1[1..]);
        ProductDropFirst(f1[1..]);
        assert product(f1[1..]) == f1[1] * product(f1[2..]);
        ProductDropFirst(f1[2..]);
        assert product(f1[2..]) == f1[2] * product(f1[3..]);
        assert product(f1[3..]) >= 1;
        assert product(f1) >= 3 * 3 * 3;
        assert false;
      }
      assert f1[0] == 2;

      // strip first factor
      ProductDropFirst(f1);
      assert product(f1) == f1[0] * product(f1[1..]);
      assert product(f1) == product(f1[1..]) * 2;
      assert product(f1[1..]) == 6;

      if |f1| > 3 {
        assert f1[1] >= 2;
        assert f1[2] >= 2;
        assert f1[3] >= 2;
        ProductDropFirst(f1[1..]);
        assert product(f1[1..]) == f1[1] * product(f1[2..]);
        ProductDropFirst(f1[2..]);
        assert product(f1[2..]) == f1[2] * product(f1[3..]);
        assert product(f1[3..]) >= 1;
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
