
type T = int

ghost function IsSorted(a: seq<T>, l: int, r: int): bool
{
  l >= 0 && r <= |a| && (l == r || l == r - 1 || (a[l] <= a[l + 1] && IsSorted(a, l + 1, r)))
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
  requires a != null
  ensures IsSorted(a[..], 0, a.Length)
  ensures IsPermutation(old(a[..]), a[..])
{
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant IsSorted(a[..], 0, i)
    invariant IsPermutation(old(a[..i]), a[..i])
  {
    var j := i;
    while j > 0 && a[j-1] > a[j]
      invariant 0 <= j <= i
      invariant IsSorted(a[..], 0, j) && IsSorted(a[..], j+1, i+1)
      invariant forall k :: j < k <= i ==> a[k] >= a[j-1]
      invariant IsPermutation(old(a[..i+1]), a[..i+1])
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
  assert IsSorted(a[..], 0, a.Length);
  assert IsPermutation(old(a[..]), a[..]);
}

method TestSortWithDups() {
  var a := new T[] [2, 1, 2];
  InsertionSort(a);
  assert IsSorted(a[..], 0, a.Length);
  assert IsPermutation(old(a[..]), a[..]);
}

