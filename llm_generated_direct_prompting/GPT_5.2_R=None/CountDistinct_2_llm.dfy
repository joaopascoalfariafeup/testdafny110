
ghost predicate SortedNondecreasing(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function DistinctCount(s: seq<int>): nat
  requires SortedNondecreasing(s)
{
  if |s| == 0 then 0 else
    1 + (if forall k :: 0 <= k < |s|-1 ==> s[k] == s[k+1] then 0 else
      DistinctCount(s[..|s|-1]) - (if s[|s|-2] == s[|s|-1] then 0 else 1))
}

ghost function DistinctCountPrefix(s: seq<int>, n: nat): nat
  requires n <= |s|
  requires SortedNondecreasing(s)
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else DistinctCountPrefix(s, n-1) + (if s[n-1] != s[n-2] then 1 else 0)
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires SortedNondecreasing(a[..])
  ensures count == DistinctCountPrefix(a[..], a.Length)
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant count == DistinctCountPrefix(a[..], i)
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
    }
    return count;
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}
