
```dafny
type T = int 

predicate IsSorted(a: array<T>)
   reads a
{
    forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
}

ghost function Inversions(a: array<T>): nat
  reads a
{
  sum i, j :: 0 <= i < j < a.Length && a[i] > a[j] ? 1 : 0
}

method RawSort(a: array<T>)
   modifies a
   ensures IsSorted(a)
   decreases Inversions(a)
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursively
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert IsSorted(a);
}
```

