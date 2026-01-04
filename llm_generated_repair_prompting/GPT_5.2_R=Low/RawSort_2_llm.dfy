/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate SortedArray(a: array<T>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

function Count(s: seq<T>, x: T): int
  decreases |s|
{
  if |s| == 0 then 0
  else Count(s[..|s|-1], x) + (if s[|s|-1] == x then 1 else 0)
}

lemma CountUpdate(s: seq<T>, idx: int, v: T, x: T)
  requires 0 <= idx < |s|
  ensures Count(s[idx := v], x) == Count(s, x) + (if v == x then 1 else 0) - (if s[idx] == x then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
  } else if idx == |s|-1 {
  } else {
    CountUpdate(s[..|s|-1], idx, v, x);
  }
}

lemma CountSwapPreserved(s: seq<T>, i: int, j: int, x: T)
  requires 0 <= i < j < |s|
  ensures Count(s[i := s[j]][j := s[i]], x) == Count(s, x)
{
  CountUpdate(s, i, s[j], x);
  var s1 := s[i := s[j]];
  assert s1[j] == s[j];
  CountUpdate(s1, j, s[i], x);
  assert s1[i] == s[j];

  if s[i] == x {
    if s[j] == x {
    } else {
    }
  } else {
    if s[j] == x {
    } else {
    }
  }
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   decreases *
   ensures SortedArray(a)
   ensures forall x: T :: Count(a[..], x) == Count(old(a[..]), x)
{
   ghost var s0 := a[..];
   assert s0 == old(a[..]);

   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var sb := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      assert a[..] == sb[i := sb[j]][j := sb[i]];
      RawSort(a); // proceed recursivelly

      assert forall x: T :: Count(a[..], x) == Count(old(a[..]), x);
      assert forall x: T :: Count(old(a[..]), x) == Count(sb[i := sb[j]][j := sb[i]], x);
      assert forall x: T :: Count(sb[i := sb[j]][j := sb[i]], x) == Count(sb, x) by {
        forall x: T
          ensures Count(sb[i := sb[j]][j := sb[i]], x) == Count(sb, x)
        {
          CountSwapPreserved(sb, i, j, x);
        }
      };
      assert forall x: T :: Count(a[..], x) == Count(sb, x);
      assert sb == s0;
      assert forall x: T :: Count(a[..], x) == Count(s0, x);
   } else {
      assert forall i0: int, j0: int :: 0 <= i0 < j0 < a.Length ==> a[i0] <= a[j0] by {
        forall i0: int, j0: int
          ensures 0 <= i0 < j0 < a.Length ==> a[i0] <= a[j0]
        {
          if 0 <= i0 < j0 < a.Length {
            if a[i0] > a[j0] {
              assert exists ii: int, jj: int :: 0 <= ii < jj < a.Length && a[ii] > a[jj] by {
                ii := i0; jj := j0;
              };
              assert false;
            }
          }
        }
      };
      assert SortedArray(a);
      assert forall x: T :: Count(a[..], x) == Count(s0, x);
   }

   assert SortedArray(a);
   assert forall x: T :: Count(a[..], x) == Count(s0, x);
   assert forall x: T :: Count(a[..], x) == Count(old(a[..]), x);
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
