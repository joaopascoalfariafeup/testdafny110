
ghost predicate SortedNondecreasing(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function DistinctSorted(s: seq<int>): nat
{
  if |s| == 0 then 0
  else if |s| == 1 then 1
  else DistinctSorted(s[..|s|-1]) + (if s[|s|-1] != s[|s|-2] then 1 else 0)
}

ghost lemma DistinctSortedExtend(s: seq<int>, x: int)
  ensures DistinctSorted(s + [x]) == (if |s| == 0 then 1 else DistinctSorted(s) + (if x != s[|s|-1] then 1 else 0))
{
  if |s| == 0 {
  } else if |s| == 1 {
  } else {
  }
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires SortedNondecreasing(a[..])
  ensures count == DistinctSorted(a[..])
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant count == DistinctSorted(a[..i])
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
        ghost {
          DistinctSortedExtend(a[..i], a[i]);
        }
    }
    return count;
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}
