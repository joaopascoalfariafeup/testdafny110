// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i :: 1 <= i < a.Length ==> a[i-1] <= a[i]
  ensures exists i :: 0 <= i < a.Length && m == a[i]
  ensures forall v :: (exists i :: 0 <= i < a.Length && v == a[i]) ==>
            (exists im :: 0 <= im < a.Length && m == a[im] &&
              (forall w :: (exists j :: 0 <= j < a.Length && w == a[j]) ==>
                ( (|set j | 0 <= j < a.Length && a[j] == w|) <= (|set j | 0 <= j < a.Length && a[j] == m|) )))
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant 1 <= best_count
      invariant 1 <= current_count
      invariant best_count <= i
      invariant current_count <= i
      invariant exists k :: 0 <= k < i && best_m == a[k]
      invariant (best_count == |set j | 0 <= j < i && a[j] == best_m|)
      invariant current_count == |set j | 0 <= j < i && a[j] == a[i-1]|
      invariant forall v :: (exists j :: 0 <= j < i && v == a[j]) ==>
                  (|set j | 0 <= j < i && a[j] == v|) <= best_count
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
