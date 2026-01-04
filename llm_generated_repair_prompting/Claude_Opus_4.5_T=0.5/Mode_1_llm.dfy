// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

ghost function Count(a: seq<int>, v: int): nat {
    if |a| == 0 then 0
    else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
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

ghost predicate IsSorted(a: seq<int>) {
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

ghost function RunLength(a: seq<int>, i: nat): nat
    requires IsSorted(a)
    requires i < |a|
{
    if i == 0 then 1
    else if a[i] == a[i-1] then 1 + RunLength(a, i-1)
    else 1
}

lemma CountInSorted(a: seq<int>, i: nat)
    requires IsSorted(a)
    requires i < |a|
    ensures Count(a[..i+1], a[i]) == RunLength(a, i)
{
    if i == 0 {
        assert a[..1] == [a[0]];
    } else {
        if a[i] == a[i-1] {
            assert a[..i+1][..i] == a[..i];
            CountInSorted(a, i-1);
        } else {
            CountDifferent(a[..i+1], a[i], i);
        }
    }
}

lemma CountDifferent(a: seq<int>, v: int, i: nat)
    requires IsSorted(a)
    requires i < |a|
    requires i > 0 ==> a[i-1] < v
    requires a[i] == v
    ensures Count(a[..i+1], v) == 1
{
    if i == 0 {
        assert a[..1] == [a[0]];
    } else {
        assert a[..i+1][..i] == a[..i];
        CountLess(a[..i], v);
    }
}

lemma CountLess(a: seq<int>, v: int)
    requires IsSorted(a)
    requires |a| > 0 ==> a[|a|-1] < v
    ensures Count(a, v) == 0
{
    if |a| > 0 {
        assert a[..|a|-1] == a[..|a|-1];
        CountLess(a[..|a|-1], v);
    }
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    requires IsSorted(a[..])
    ensures exists i :: 0 <= i < a.Length && a[i] == m
    ensures Count(a[..], m) >= 1
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
        invariant 1 <= best_count
        invariant 1 <= current_count
        invariant exists j :: 0 <= j < a.Length && a[j] == best_m
        invariant current_count == RunLength(a[..], i-1)
        invariant best_count >= current_count || best_count >= 1
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
