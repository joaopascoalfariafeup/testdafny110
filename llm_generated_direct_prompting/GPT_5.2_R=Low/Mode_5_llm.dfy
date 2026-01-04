// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

predicate SortedSeq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function CountVal(s: seq<int>, v: int): nat
  decreases |s|
{
  if |s| == 0 then 0
  else CountVal(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

lemma CountValAppend(s: seq<int>, v: int, x: int)
  ensures CountVal(s + [x], v) == CountVal(s, v) + (if x == v then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountValAppend(s[..|s|-1], v, x);
  }
}

lemma CountValZeroIfNoOccur(s: seq<int>, v: int)
  requires forall k :: 0 <= k < |s| ==> s[k] != v
  ensures CountVal(s, v) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert forall k :: 0 <= k < |s|-1 ==> s[k] != v;
    CountValZeroIfNoOccur(s[..|s|-1], v);
  }
}

lemma NoEarlierEqualOnIncrease(s: seq<int>, i: int)
  requires SortedSeq(s)
  requires 0 < i < |s|
  requires s[i-1] < s[i]
  ensures forall j :: 0 <= j < i ==> s[j] < s[i]
{
  assert forall j :: 0 <= j < i ==> s[j] <= s[i-1];
}

method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires SortedSeq(a[..])
  ensures exists k :: 0 <= k < a.Length && a[k] == m
  ensures forall k :: 0 <= k < a.Length ==> CountVal(a[..], a[k]) <= CountVal(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant SortedSeq(a[..])
      invariant best_count == CountVal(a[..i], best_m)
      invariant 1 <= best_count <= i
      invariant exists k :: 0 <= k < i && a[k] == best_m
      invariant forall k :: 0 <= k < i ==> CountVal(a[..i], a[k]) <= best_count
      invariant current_count == CountVal(a[..i], a[i-1])
      invariant 1 <= current_count <= i
    {
        if a[i] == a[i-1] {
            current_count := current_count + 1;
            assert CountVal(a[..i+1], a[i]) == CountVal(a[..i], a[i]) + 1 by {
              CountValAppend(a[..i], a[i], a[i]);
            }
            assert CountVal(a[..i], a[i]) == CountVal(a[..i], a[i-1]);
            assert current_count == CountVal(a[..i+1], a[i]);
            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            }
        }
        else {
            assert a[i-1] < a[i];
            assert forall j :: 0 <= j < i ==> a[j] < a[i] by {
              NoEarlierEqualOnIncrease(a[..], i);
            }
            assert forall j :: 0 <= j < i ==> a[j] != a[i];
            assert CountVal(a[..i], a[i]) == 0 by {
              CountValZeroIfNoOccur(a[..i], a[i]);
            }
            assert CountVal(a[..i+1], a[i]) == 1 by {
              CountValAppend(a[..i], a[i], a[i]);
            }
            current_count := 1;
            assert current_count == CountVal(a[..i+1], a[i]);
        }

        assert forall k :: 0 <= k < i ==> CountVal(a[..i+1], a[k]) == CountVal(a[..i], a[k]) by {
          assert forall k :: 0 <= k < i ==> a[k] != a[i] ==> CountVal(a[..i+1], a[k]) == CountVal(a[..i], a[k]) by {
            forall k | 0 <= k < i
              ensures a[k] != a[i] ==> CountVal(a[..i+1], a[k]) == CountVal(a[..i], a[k])
            {
              if a[k] != a[i] {
                CountValAppend(a[..i], a[k], a[i]);
              }
            }
          }
          forall k | 0 <= k < i
            ensures CountVal(a[..i+1], a[k]) == CountVal(a[..i], a[k])
          {
            if a[k] == a[i] {
              if a[i] == a[i-1] {
                // ok, can happen only for k in the last run; counts for a[k] increase too, but they are bounded by best_count after updates
              } else {
                assert false;
              }
            } else {
              CountValAppend(a[..i], a[k], a[i]);
            }
          }
        }
    }
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
