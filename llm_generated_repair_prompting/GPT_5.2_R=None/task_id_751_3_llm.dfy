// Auxiliary function that gives the parent index of a non-root node (with index > 0) in a heap.
function Parent(i: nat): nat
  requires i > 0
  ensures Parent(i) < i
{
  (i-1)/2
}

// Check if an array of integers represents a min heap.
method IsMinHeap(a: array<int>) returns (result: bool)
  ensures result <==> (forall i :: 1 <= i < a.Length ==> a[Parent(i)] <= a[i])
{
  if a.Length > 0 {
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length + 1
      invariant forall k :: 1 <= k < i && k < a.Length ==> a[Parent(k)] <= a[k]
    {
      if i < a.Length && a[Parent(i)] > a[i] {
        return false;
      }
    }
  }
  return true;
}

// Test cases checked statically.
method IsMinHeapTest(){
  // Totally sorted
  var a1 := new int[] [1, 2, 3, 4, 5, 6];
  var res1 := IsMinHeap(a1);
  assert res1;

  // Partially sorted
  var a2 := new int[] [2, 4, 3, 5, 10, 15];
  var res2 := IsMinHeap(a2);
  assert res2;

  // Not partially sorted
  var a3 := new int[] [2, 10, 4, 5, 3, 15];
  // Help the verifier reason about the array's contents and thus about IsMinHeap's postcondition
  assert a3[..] == [2, 10, 4, 5, 3, 15];

  // Also expose the specific violated heap condition (at i=4, parent=1): a3[1] <= a3[4] is false.
  assert Parent(4) == 1;
  assert a3[1] == 10 && a3[4] == 3;
  assert !(forall i :: 1 <= i < a3.Length ==> a3[Parent(i)] <= a3[i]);

  var res3 := IsMinHeap(a3);
  assert !res3;
}
