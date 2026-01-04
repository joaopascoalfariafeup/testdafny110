// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

ghost function Count(a: seq<int>, x: int): nat {
    if |a| == 0 then 0
    else (if a[|a|-1] == x then 1 else 0) + Count(a[..|a|-1], x)
}

ghost predicate IsSorted(a: seq<int>) {
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

ghost function RunLength(a: seq<int>, i: nat): nat
    requires IsSorted(a)
    requires 0 < i <= |a|
{
    if i == 1 then 1
    else if a[i-1] == a[i-2] then 1 + RunLength(a, i-1)
    else 1
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    requires IsSorted(a[..])
    ensures exists i :: 0 <= i < a.Length && a[i] == m
    ensures forall x :: Count(a[..], x) <= Count(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
        invariant 1 <= current_count <= i
        invariant 1 <= best_count <= i
        invariant exists j :: 0 <= j < i && a[j] == best_m
        invariant current_count == RunLength(a[..], i)
        invariant forall x :: Count(a[..i], x) <= best_count
        invariant Count(a[..i], best_m) == best_count
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
