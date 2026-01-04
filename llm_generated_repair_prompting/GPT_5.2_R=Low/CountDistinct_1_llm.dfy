
ghost function Transitions(s: seq<int>): set<int>
{
  set i:int | 1 <= i < |s| && s[i] != s[i-1]
}

ghost function RunsCount(s: seq<int>): nat
{
  if |s| == 0 then 0 else (1 + |Transitions(s)|) as nat
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  ensures count == RunsCount(a[..])
  ensures count <= a.Length
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= count <= i
      invariant count == (1 + |set j:int | 1 <= j < i && a[j] != a[j-1]|) as nat
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
