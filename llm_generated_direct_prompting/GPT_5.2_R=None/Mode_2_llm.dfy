// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i :: 0 < i < a.Length ==> a[i-1] <= a[i]
  ensures exists i :: 0 <= i < a.Length && m == a[i]
  ensures forall v :: (exists i :: 0 <= i < a.Length && v == a[i]) ==>
            (exists i :: 0 <= i < a.Length && m == a[i]) &&
            (forall s, t :: 0 <= s <= t < a.Length && a[s] == v ==>
                t - s + 1 <=
                (exists u, w :: 0 <= u <= w < a.Length && a[u] == m && a[w] == m && w - u + 1 >= t - s + 1))
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= best_count
      invariant 1 <= current_count
      invariant exists j :: 0 <= j < i && best_m == a[j]
      invariant forall k :: 0 <= k < i ==> best_count >= 1
      invariant forall s, t :: 0 <= s <= t < i && a[s] == a[t] ==>
                t - s + 1 <= best_count
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
