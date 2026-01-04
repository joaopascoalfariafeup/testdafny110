predicate IsSorted(a: array<int>)
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    requires IsSorted(a)
    ensures exists i :: 0 <= i < a.Length && a[i] == m
    ensures forall i, j :: 0 <= i <= j < a.Length && a[i] == a[j] ==> j - i + 1 <= a.Length
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
        invariant 1 <= i <= a.Length
        invariant 1 <= best_count <= i
        invariant 1 <= current_count <= i
        invariant exists k :: 0 <= k < i && a[k] == best_m
        invariant forall k, l :: 0 <= k <= l < i && a[k] == a[l] ==> l - k + 1 <= best_count
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
