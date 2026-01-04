/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Auxiliary ghost function to check if a sequence is sorted
ghost function IsSorted(a: seq<int>): bool
{
  forall i :: 0 <= i < |a|-1 ==> a[i] <= a[i+1]
}

// Auxiliary ghost function to check if two sequences are permutations of each other
ghost function IsPermutation(a: seq<int>, b: seq<int>): bool
{
  |a| == |b| && (forall i :: 0 <= i < |a| ==> mult(a, a[i]) == mult(b, a[i]))
}

// Auxiliary ghost function to calculate the multiplicity of an element in a sequence
ghost function mult(a: seq<int>, v: int): nat
{
  if |a| == 0 then 0 else (if a[0] == v then 1 else 0) + mult(a[1..], v)
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..]) && IsPermutation(old(a[..]), a[..])
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 1 <= n <= a.Length
    invariant IsPermutation(old(a[..]), a[..])
    invariant IsSorted(a[n..])
    invariant forall k :: 0 <= k < n-1 ==> a[k] <= a[n-1]
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant IsPermutation(old(a[..]), a[..])
      invariant forall k :: 0 <= k < i-1 ==> a[k] <= a[i-1]
      invariant newn == 0 || a[newn-1] <= a[newn]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }
    n := newn;
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
 }
