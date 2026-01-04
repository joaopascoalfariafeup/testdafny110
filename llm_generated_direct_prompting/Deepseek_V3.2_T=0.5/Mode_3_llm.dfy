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
      invariant current_count == CountSegment(a, i-1)
      invariant best_count == MaxCountSegment(a, i-1)
      invariant exists k :: 0 <= k < i && a[k] == best_m
      invariant forall k :: 0 <= k < i ==> CountSegment(a, k) <= best_count
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

function CountSegment(a: array<int>, idx: int): int
  requires 0 <= idx < a.Length
  reads a
{
  if idx == 0 then 1 else
    if a[idx] == a[idx-1] then CountSegment(a, idx-1) + 1 else 1
}

function MaxCountSegment(a: array<int>, idx: int): int
  requires 0 <= idx < a.Length
  reads a
{
  if idx == 0 then 1 else
    var prev := MaxCountSegment(a, idx-1);
    var cur := CountSegment(a, idx);
    if cur > prev then cur else prev
}

function Count(a: array<int>, value: int): int
  reads a
{
  if a.Length == 0 then 0 else CountFrom(a, value, a.Length-1)
}

function CountFrom(a: array<int>, value: int, idx: int): int
  requires -1 <= idx < a.Length
  reads a
  decreases idx
{
  if idx < 0 then 0 else
    (if a[idx] == value then 1 else 0) + CountFrom(a, value, idx-1)
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
