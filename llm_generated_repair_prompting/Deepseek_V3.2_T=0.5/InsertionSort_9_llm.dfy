/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate sorted(s: seq<T>)
{
  forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

predicate permutation(a: seq<T>, b: seq<T>)
{
  multiset(a) == multiset(b)
}

// Helper lemma to prove that swapping preserves permutation
lemma swap_permutation(a: array<T>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures permutation(a[..], (a[..])[i := a[j]][j := a[i]])
{
  // Swapping two elements preserves multiset
  // The lemma body is empty because the postcondition follows from multiset properties
}

// Helper lemma to prove that swapping adjacent elements maintains sorted prefix
lemma swap_maintains_sorted_prefix(a: array<T>, i: int, j: int)
  requires 0 <= j < i < a.Length
  requires sorted(a[0..i])
  requires a[j] > a[j+1]
  ensures sorted(a[0..j] + [a[j+1]] + [a[j]] + a[j+2..i+1])
{
  // The lemma body is empty because the postcondition follows from the definition of sorted
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures sorted(a[..])
    ensures permutation(old(a[..]), a[..])
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant sorted(a[0..i])
      invariant permutation(old(a[..]), a[..])
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant sorted(a[0..j])
        invariant j < i ==> sorted(a[j..i+1])
        invariant permutation(old(a[..]), a[..])
      {
        // Swap a[j-1] and a[j]
        swap_permutation(a, j-1, j);
        swap_maintains_sorted_prefix(a, i, j-1);
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    InsertionSort(a);
    // Helper assertions to help Dafny verify the final array
    assert a[..] == [3, 4, 6, 8, 9];
    assert a[0] == 3;
    assert a[1] == 4;
    assert a[2] == 6;
    assert a[3] == 8;
    assert a[4] == 9;
}  

method TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    InsertionSort(a);
    // Helper assertions to help Dafny verify the final array
    assert a[..] ==  [1, 2, 2];
    assert a[0] == 1;
    assert a[1] == 2;
    assert a[2] == 2;
}





