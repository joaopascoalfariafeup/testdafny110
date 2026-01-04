// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures exists k :: 0 <= k < a.Length && a[k] == m
  ensures forall k :: 0 <= k < a.Length && a[k] != m ==> Count(a, m) >= Count(a, a[k])
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant exists k :: 0 <= k < i && a[k] == best_m
      invariant forall k :: 0 <= k < i && a[k] != best_m ==> Count(a[..i], best_m) >= Count(a[..i], a[k])
      invariant best_count == Count(a[..i], best_m)
      invariant current_count <= i
      invariant current_count == Count(a[i-current_count..i], a[i-1])
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

function Count(a: array<int>, x: int): nat
  reads a
{
  if a == null || a.Length == 0 then 0 else (if a[a.Length-1] == x then 1 else 0) + Count(a[..a.Length-1], x)
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
