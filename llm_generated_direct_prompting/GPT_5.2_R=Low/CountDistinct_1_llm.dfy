
predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function DistinctSet(s: seq<int>): set<int>
{
  set x | exists i :: 0 <= i < |s| && s[i] == x
}

function RunCount(s: seq<int>): nat
{
  if |s| == 0 then 0
  else if |s| == 1 then 1
  else RunCount(s[..|s|-1]) + (if s[|s|-1] != s[|s|-2] then 1 else 0)
}

lemma AddFreshCardinality(S: set<int>, x: int)
  ensures x !in S ==> |S + {x}| == |S| + 1
{
}

lemma RunCountEqualsDistinctCard(s: seq<int>)
  requires Sorted(s)
  ensures RunCount(s) == |DistinctSet(s)|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    var t := s[..|s|-1];
    RunCountEqualsDistinctCard(t);

    assert Sorted(t);

    var last := s[|s|-1];
    var prev := s[|s|-2];

    if last == prev {
      assert last in DistinctSet(t);
      assert DistinctSet(s) == DistinctSet(t);
    } else {
      assert prev < last;
      assert forall i :: 0 <= i < |t| ==> s[i] <= prev;
      assert forall i :: 0 <= i < |t| ==> s[i] != last;
      assert last !in DistinctSet(t);
      assert DistinctSet(s) == DistinctSet(t) + {last};
      AddFreshCardinality(DistinctSet(t), last);
    }
  }
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires Sorted(a[..])
  ensures count == |DistinctSet(a[..])|
  ensures count <= a.Length
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant count == RunCount(a[..i])
      invariant count <= i
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
        assert RunCount(a[..i+1]) == RunCount(a[..i]) + (if a[i] != a[i-1] then 1 else 0);
        assert count == RunCount(a[..i+1]);
    }
    assert count == RunCount(a[..a.Length]);
    RunCountEqualsDistinctCard(a[..]);
    assert count == |DistinctSet(a[..])|;
    return count;
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}
