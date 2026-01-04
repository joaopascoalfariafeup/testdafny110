// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

function Max(x: nat, y: nat): nat {
  if x >= y then x else y
}

predicate SortedArray(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

function RunLenEnd(s: seq<int>, idx: nat): nat
  requires 0 <= idx < |s|
  decreases idx
{
  if idx == 0 then 1
  else if s[idx] == s[idx - 1] then RunLenEnd(s, idx - 1) + 1
  else 1
}

method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires SortedArray(a)
  ensures exists k :: 0 <= k < a.Length && m == a[k] &&
            (forall j :: 0 <= j < a.Length ==> RunLenEnd(a[..], j) <= RunLenEnd(a[..], k))
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant current_count == RunLenEnd(a[..], i - 1)
      invariant best_count >= 1
      invariant current_count >= 1
      invariant forall j :: 0 <= j < i ==> RunLenEnd(a[..], j) <= best_count
      invariant exists k :: 0 <= k < i && best_m == a[k] && best_count == RunLenEnd(a[..], k)
    {
        if a[i] == a[i-1] {
            current_count := current_count + 1;
            assert current_count == RunLenEnd(a[..], i);
            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
                assert best_count == RunLenEnd(a[..], i);
            }
        }
        else {
            current_count := 1;
            assert current_count == RunLenEnd(a[..], i);
        }
    }
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
