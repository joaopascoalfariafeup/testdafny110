/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Insert(x: int, s: seq<int>): seq<int>
  requires Sorted(s)
  decreases |s|
{
  if |s| == 0 then
    [x]
  else if x <= s[0] then
    [x] + s
  else
    [s[0]] + Insert(x, s[1..])
}

function Sort(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else Insert(s[0], Sort(s[1..]))
}

lemma {:axiom} SortSpec(s: seq<int>)
  ensures Sorted(Sort(s))
  ensures multiset(Sort(s)) == multiset(s)

lemma {:axiom} SortSameMultiset(s: seq<int>, t: seq<int>)
  requires multiset(s) == multiset(t)
  ensures Sort(s) == Sort(t)

lemma {:axiom} SortIdOnSorted(s: seq<int>)
  requires Sorted(s)
  ensures Sort(s) == s


// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   decreases *
   ensures a[..] == Sort(old(a[..]))
   ensures multiset(a[..]) == multiset(old(a[..]))
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursivelly
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
