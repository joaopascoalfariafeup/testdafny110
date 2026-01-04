// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutions exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> 
    (count(a[..], a[i]) <= count(a[..], m) && 
    (count(a[..], a[i]) == count(a[..], m) ==> a[i] <= m))
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> 
        (count(a[..i], a[j]) <= best_count && 
        (count(a[..i], a[j]) == best_count ==> a[j] <= best_m))
      invariant 0 < best_count <= i
      invariant best_count == count(a[..i], best_m)
      decreases a.Length - i
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

function count(a: seq<int>, num: int): nat
{
  if |a| == 0 then 0 
  else (if a[0] == num then 1 else 0) + count(a[1..], num)
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}

