
predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function DistinctCountUpTo(s: seq<int>, n: nat): nat
  requires n <= |s|
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else DistinctCountUpTo(s, n - 1) + (if s[n - 1] != s[n - 2] then 1 else 0)
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires Sorted(a[..])
  ensures count == DistinctCountUpTo(a[..], a.Length)
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant count == DistinctCountUpTo(a[..], i)
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
