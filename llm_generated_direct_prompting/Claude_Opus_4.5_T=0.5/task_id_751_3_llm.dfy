// Check if an array of integers represents a min heap.
ghost predicate IsMinHeapProp(a: array<int>, n: nat)
  reads a
  requires n <= a.Length
{
  forall i :: 1 <= i < n ==> a[Parent(i)] <= a[i]
}

method IsMinHeap(a: array<int>) returns (result: bool)
  ensures result <==> IsMinHeapProp(a, a.Length)
{
  if a.Length > 0 {
    for i := 1 to a.Length 
      invariant IsMinHeapProp(a, i)
    {
      if a[Parent(i)] > a[i] {
        return false;
      }
    }
  }
  return true;
}

// Auxiliary function that gives the parent index of a non-root node (with index > 0) in a heap.
function Parent(i: nat): nat
  requires i > 0
{ 
  (i-1)/2 
}

// Test cases checked statically.
method IsMinHeapTest(){
  // Totally sorted
  var a1:= new int[] [1, 2, 3, 4, 5, 6];
  var res1:=IsMinHeap(a1);
  assert IsMinHeapProp(a1, a1.Length);
  assert res1;

  // Partially sorted
  var a2:= new int[] [2, 4, 3, 5, 10, 15];
  var res2 := IsMinHeap(a2);
  assert IsMinHeapProp(a2, a2.Length);
  assert res2;

  // Not partially sorted
  var a3:= new int[] [2, 10, 4, 5, 3, 15];
  var res3 := IsMinHeap(a3);
  assert a3[Parent(4)] > a3[4];
  assert !IsMinHeapProp(a3, a3.Length);
  assert !res3;


}
