// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures exists k :: 0 <= k < a.Length && a[k] == m
  ensures forall k :: 0 <= k < a.Length ==> Count(a, m) >= Count(a, a[k])
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant current_count == CountSegment(a, 0, i)
      invariant best_count == CountSegment(a, 0, i, best_m)
      invariant forall k :: 0 <= k < i ==> best_count >= CountSegment(a, 0, i, a[k])
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

function CountSegment(a: array<int>, lo: int, hi: int, x: int): int
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  if lo == hi then 0
  else (if a[lo] == x then 1 else 0) + CountSegment(a, lo+1, hi, x)
}

function CountSegment(a: array<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= a.Length
  requires forall i, j :: lo <= i < j < hi ==> a[i] == a[j]
  reads a
{
  if lo == hi then 0 else 1 + CountSegment(a, lo+1, hi)
}

function Count(a: array<int>, x: int): int
  requires a.Length > 0
  reads a
{
  CountSegment(a, 0, a.Length, x)
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
