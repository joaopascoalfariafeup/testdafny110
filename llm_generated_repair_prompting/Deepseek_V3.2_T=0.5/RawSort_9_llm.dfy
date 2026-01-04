/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate permutation(a: seq<T>, b: seq<T>)
{
  |a| == |b| &&
  (multiset(a) == multiset(b))
}

// Helper function to measure progress: number of inversions in the array
function inversions(s: seq<T>): int
{
  if |s| <= 1 then 0
  else
    inversions(s[..|s|-1]) +
    (|{ k | 0 <= k < |s|-1 && s[k] > s[|s|-1] }| as int)
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures sorted(a[..])
   ensures permutation(old(a[..]), a[..])
   decreases inversions(a[..])
{
   if exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]  {
      var i, j :| 0 <= i < j < a.Length && a[i] > a[j];
      a[i], a[j] := a[j], a[i]; // swap
      // Show that inversions decreases
      assert inversions(a[..]) < inversions(old(a[..]));
      RawSort(a); // proceed recursively
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   // Helper assertions to help Dafny prove the final order
   assert a[0] == 1;
   assert a[1] == 3;
   assert a[2] == 5;
   assert a[..] == [1, 3, 5];
}








