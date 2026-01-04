// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i :: 0 < i < a.Length ==> a[i-1] <= a[i]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
  ensures forall v :: (exists k :: 0 <= k < a.Length && v == a[k]) ==>
            (forall c :: (exists k :: 0 <= k < a.Length && c == a[k]) ==>
                CountOcc(a, v) >= CountOcc(a, c))
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= current_count
      invariant 1 <= best_count
      invariant exists k :: 0 <= k < i && best_m == a[k]
      invariant best_count == CountOccPrefix(a, i, best_m)
      invariant forall v :: (exists k :: 0 <= k < i && v == a[k]) ==>
                  CountOccPrefix(a, i, best_m) >= CountOccPrefix(a, i, v)
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

function CountOccPrefix(a: array<int>, n: int, v: int): int
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0 else CountOccPrefix(a, n-1, v) + (if a[n-1] == v then 1 else 0)
}

function CountOcc(a: array<int>, v: int): int
  requires a != null
  reads a
{
  CountOccPrefix(a, a.Length, v)
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
