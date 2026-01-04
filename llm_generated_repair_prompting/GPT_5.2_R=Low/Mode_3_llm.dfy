// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

predicate Sorted(s: seq<int>)
{
  forall i: nat, j: nat :: i < j < |s| ==> s[i] <= s[j]
}

function MaxNat(x: nat, y: nat): nat
{
  if x >= y then x else y
}

lemma MaxNatGeLeft(x: nat, y: nat)
  ensures x <= MaxNat(x, y)
{
}

lemma MaxNatGeRight(x: nat, y: nat)
  ensures y <= MaxNat(x, y)
{
}

function RunLenEndingAt(s: seq<int>, n: nat): nat
  requires 0 < n <= |s|
  decreases n
{
  if n == 1 then 1
  else if s[n-1] == s[n-2] then 1 + RunLenEndingAt(s, n-1)
  else 1
}

function MaxRunLen(s: seq<int>, n: nat): nat
  requires n <= |s|
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else MaxNat(MaxRunLen(s, n-1), RunLenEndingAt(s, n))
}

lemma MaxRunLenUpperBound(s: seq<int>, n: nat)
  requires n <= |s|
  ensures forall k: nat :: 1 <= k <= n ==> RunLenEndingAt(s, k) <= MaxRunLen(s, n)
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    MaxRunLenUpperBound(s, n-1);

    assert MaxRunLen(s, n) == MaxNat(MaxRunLen(s, n-1), RunLenEndingAt(s, n));
    MaxNatGeLeft(MaxRunLen(s, n-1), RunLenEndingAt(s, n));
    MaxNatGeRight(MaxRunLen(s, n-1), RunLenEndingAt(s, n));

    // Establish the quantified postcondition by proving it for an arbitrary k
    assert forall k: nat :: 1 <= k <= n ==> RunLenEndingAt(s, k) <= MaxRunLen(s, n) by {
      forall k: nat | 1 <= k <= n
        ensures RunLenEndingAt(s, k) <= MaxRunLen(s, n)
      {
        if k == n {
          // RunLenEndingAt(s,n) <= MaxNat(MaxRunLen(s,n-1), RunLenEndingAt(s,n)) == MaxRunLen(s,n)
          // follows from MaxNatGeRight and the asserted definition above
        } else {
          assert 1 <= k <= n-1;
          // From IH: RunLenEndingAt(s,k) <= MaxRunLen(s,n-1)
          // and MaxRunLen(s,n-1) <= MaxRunLen(s,n) via MaxNatGeLeft
        }
      }
    }
  }
}

method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires Sorted(a[..a.Length])
  ensures exists k: nat :: 1 <= k <= a.Length && a[k-1] == m && RunLenEndingAt(a[..a.Length], k) == MaxRunLen(a[..a.Length], a.Length)
  ensures forall k: nat :: 1 <= k <= a.Length ==> RunLenEndingAt(a[..a.Length], k) <= MaxRunLen(a[..a.Length], a.Length)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    var s := a[..a.Length];
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant current_count == RunLenEndingAt(s, i)
      invariant best_count == MaxRunLen(s, i)
      invariant exists k: nat :: 1 <= k <= i && s[k-1] == best_m && RunLenEndingAt(s, k) == best_count
    {
        ghost var prevBest := best_count;

        if a[i] == a[i-1] {
            current_count := current_count + 1;
            assert current_count == RunLenEndingAt(s, i+1);
            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            }
        }
        else {
            current_count := 1;
            assert current_count == RunLenEndingAt(s, i+1);
        }
        assert best_count == MaxNat(prevBest, current_count);
        assert MaxRunLen(s, i+1) == MaxNat(MaxRunLen(s, i), RunLenEndingAt(s, i+1));
        assert best_count == MaxRunLen(s, i+1);
    }

    // Prove the universal upper-bound postcondition for the full length
    MaxRunLenUpperBound(s, a.Length);

    return best_m;
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
