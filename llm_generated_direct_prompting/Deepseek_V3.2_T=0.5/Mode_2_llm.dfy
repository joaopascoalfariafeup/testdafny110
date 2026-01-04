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

ghost function CountSegment(a: array<int>, idx: int): int
  requires a.Length > 0
  requires 0 <= idx < a.Length
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  reads a
{
  if idx == 0 then 1 else
    if a[idx] == a[idx-1] then CountSegment(a, idx-1) + 1 else 1
}

ghost function MaxCountSegment(a: array<int>, idx: int): int
  requires a.Length > 0
  requires 0 <= idx < a.Length
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  reads a
{
  if idx == 0 then 1 else
    var prev := MaxCountSegment(a, idx-1);
    var cur := CountSegment(a, idx);
    if cur > prev then cur else prev
}

ghost function Count(a: array<int>, value: int): int
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  reads a
{
  CountHelper(a, value, a.Length)
}

ghost function CountHelper(a: array<int>, value: int, n: int): int
  requires a.Length > 0
  requires 0 <= n <= a.Length
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  reads a
  decreases n
{
  if n == 0 then 0 else
    CountHelper(a, value, n-1) + (if a[n-1] == value then 1 else 0)
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
