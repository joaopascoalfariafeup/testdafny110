// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

ghost function Count(a: seq<int>, v: int): int
{
    if |a| == 0 then 0
    else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

ghost predicate IsMode(a: seq<int>, m: int)
{
    exists i :: 0 <= i < |a| && a[i] == m && forall v :: Count(a, v) <= Count(a, m)
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && a[i] == m
    ensures forall v :: Count(a[..], v) <= Count(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
        invariant 1 <= current_count
        invariant 1 <= best_count
        invariant exists j :: 0 <= j < i && a[j] == best_m
        invariant best_count == Count(a[..i], best_m)
        invariant forall v :: Count(a[..i], v) <= best_count
        invariant i > 0 ==> current_count == Count(a[..i], a[i-1])
        invariant i > 0 ==> (forall k :: 0 <= k < i - current_count ==> a[k] != a[i-1])
    {
        if a[i] == a[i-1] {
            current_count := current_count + 1;
            assert a[..i+1] == a[..i] + [a[i]];
            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            }
        }
        else {
            assert a[..i+1] == a[..i] + [a[i]];
            current_count := 1;
        }
    }
    assert a[..a.Length] == a[..];
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert a[..] == [1, 1, 2, 2, 3];
    assert Count([1, 1, 2, 2, 3], 1) == 2;
    assert Count([1, 1, 2, 2, 3], 2) == 2;
    assert m == 1 || m == 2;
}
