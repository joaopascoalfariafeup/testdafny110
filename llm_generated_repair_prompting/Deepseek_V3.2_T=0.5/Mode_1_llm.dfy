// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
  ensures exists k :: 0 <= k < a.Length && a[k] == m
  ensures forall k :: 0 <= k < a.Length ==> Count(a[..], a[k]) <= Count(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant current_count == Count(a[i-current_count..i], a[i-1])
      invariant best_count == Count(a[..i], best_m)
      invariant forall k :: 0 <= k < i ==> Count(a[..i], a[k]) <= best_count
      invariant exists k :: 0 <= k < i && a[k] == best_m
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
    m := best_m;
}

function Count(s: seq<int>, x: int): int
  ensures Count(s, x) >= 0
{
  if |s| == 0 then 0 else (if s[|s|-1] == x then 1 else 0) + Count(s[..|s|-1], x)
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
