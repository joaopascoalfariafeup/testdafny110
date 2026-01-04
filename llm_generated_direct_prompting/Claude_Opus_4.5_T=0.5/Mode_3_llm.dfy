// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

ghost function Count(a: seq<int>, v: int): nat {
    if |a| == 0 then 0
    else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

ghost predicate IsMode(a: seq<int>, m: int) {
    exists i :: 0 <= i < |a| && a[i] == m && forall v :: Count(a, v) <= Count(a, m)
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && a[i] == m
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
        invariant 1 <= best_count
        invariant 1 <= current_count
        invariant exists j :: 0 <= j < a.Length && a[j] == best_m
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
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
