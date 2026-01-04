
ghost function IsSorted(s: seq<int>): bool
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

method BubbleSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures forall i :: 0 <= i < a.Length ==> old(a[..]).Contains(a[i])
  ensures forall i :: 0 <= i < old(a.Length) ==> a[..].Contains(old(a[..])[i])
{
  var n := a.Length; 

  while n  > 1
    invariant 1 <= n <= a.Length
    invariant IsSorted(a[n..])
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i :: 0 <= i < a.Length ==> old(a[..]).Contains(a[i])
    invariant forall i :: 0 <= i < old(a.Length) ==> a[..].Contains(old(a[..])[i])
  {
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n+1
      invariant forall j :: 0 <= j < i-1 ==> a[j] <= a[j+1]
      invariant forall j :: 0 <= j < i ==> a[j] <= a[i-1]
      invariant forall j :: i < j < n ==> a[i-1] <= a[j]
      invariant newn == 0 || (newn < i && a[newn-1] > a[newn])
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }
    n := newn;
  }
}

method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
 }

