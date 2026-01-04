// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

ghost function Count(a: seq<int>, x: int): nat {
    if |a| == 0 then 0
    else (if a[|a|-1] == x then 1 else 0) + Count(a[..|a|-1], x)
}

ghost function MaxCount(a: seq<int>): nat 
    requires |a| > 0
{
    if |a| == 1 then 1
    else 
        var prevMax := MaxCount(a[..|a|-1]);
        var currCount := Count(a, a[|a|-1]);
        if currCount > prevMax then currCount else prevMax
}

ghost predicate IsMode(a: seq<int>, m: int)
    requires |a| > 0
{
    m in a && Count(a, m) == MaxCount(a)
}

ghost function RunLength(a: seq<int>, i: nat): nat
    requires |a| > 0
    requires 0 <= i < |a|
{
    if i == 0 then 1
    else if a[i] == a[i-1] then 1 + RunLength(a, i-1)
    else 1
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures m in a[..]
    ensures exists k :: 0 <= k < a.Length && a[k] == m && Count(a[..], m) >= Count(a[..], a[k])
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
        invariant 1 <= best_count
        invariant 1 <= current_count
        invariant best_m in a[..i]
        invariant current_count == RunLength(a[..], i-1)
        invariant best_count >= current_count || a[i-1] == best_m
        invariant Count(a[..i], best_m) >= best_count
        invariant forall j :: 0 <= j < i ==> Count(a[..i], a[j]) <= best_count
    {
        if a[i] == a[i-1] {
            current_count := current_count + 1;
            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            }
        }
        else {
            current_count := 1;
        }
    }
    assert a[..a.Length] == a[..];
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
