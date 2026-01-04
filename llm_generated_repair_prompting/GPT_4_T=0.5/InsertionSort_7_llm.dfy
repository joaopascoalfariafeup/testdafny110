
type T = int

ghost function IsSorted(a: array<T>, l: int, r: int): bool
  reads a
{
  forall i :: l <= i < r ==> a[i] <= a[i+1]
}

ghost function IsPermutation(a: seq<T>, b: seq<T>): bool
{
  |a| == |b| && forall x :: x in a ==> mult(a, x) == mult(b, x)
}

ghost function mult(s: seq<T>, x: T): nat
{
  if |s| == 0 then 0 else (if s[0] == x then 1 else 0) + mult(s[1..], x)
}

method InsertionSort(a: array<T>)
  modifies a
  ensures IsSorted(a, 0, a.Length)
  ensures IsPermutation(old(a[..]), a[..])
{
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant IsSorted(a, 0, i)
    invariant IsPermutation(old(a[..]), a[..])
  {
    var j := i;
    while j > 0 && a[j-1] > a[j]
      invariant 0 <= j <= i
      invariant IsSorted(a, 0, j)
      invariant IsSorted(a, j, i)
      invariant forall k :: j <= k <= i ==> a[k] >= a[j]
      invariant IsPermutation(old(a[..]), a[..])
      decreases j
    {
      a[j-1], a[j] := a[j], a[j-1];
      j := j - 1;
    }
  }
}

method TestSortSimple() {
  var a := new T[] [9, 4, 6, 3, 8];
  InsertionSort(a);
  assert a[..] == [3, 4, 6, 8, 9];
}

method TestSortWithDups() {
  var a := new T[] [2, 1, 2];
  InsertionSort(a);
  assert a[..] == [1, 2, 2];
}

