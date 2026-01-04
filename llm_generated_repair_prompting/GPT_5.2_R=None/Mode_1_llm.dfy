// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i :: 0 < i < a.Length ==> a[i-1] <= a[i]
  ensures exists i :: 0 <= i < a.Length && m == a[i]
  ensures forall v :: (exists j :: 0 <= j < a.Length && v == a[j]) ==>
            (var cm := |set j | 0 <= j < a.Length && a[j] == m|;
             var cv := |set j | 0 <= j < a.Length && a[j] == v|;
             cm >= cv)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= best_count
      invariant 1 <= current_count
      invariant exists j :: 0 <= j < i && best_m == a[j]
      invariant best_count <= i
      invariant current_count <= i
      invariant exists s :: 0 <= s <= i-1 &&
                 current_count == |set j | s <= j <= i-1 && a[j] == a[i-1]|
      invariant forall v :: (exists j :: 0 <= j < i && v == a[j]) ==>
                (var cb := |set j | 0 <= j < i && a[j] == best_m|;
                 var cv := |set j | 0 <= j < i && a[j] == v|;
                 cb >= cv)
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
