
// Check if an array of integers represents a min heap.
method IsMinHeap(a: array<int>) returns (result: bool)
  ensures result ==> (forall i :: 0 <= i < a.Length/2 ==> a[i] <= a[2*i+1] && (2*i+2 < a.Length ==> a[i] <= a[2*i+2]))
  ensures !result ==> (exists i :: 0 <= i < a.Length/2 && (a[i] > a[2*i+1] || (2*i+2 < a.Length && a[i] > a[2*i+2])))
  ensures (forall i :: 0 <= i < a.Length/2 ==> a[i] <= a[2*i+1] && (2*i+2 < a.Length ==> a[i] <= a[2*i+2])) <==> result
{
  if a.Length > 0 {
    for i := 0 to a.Length/2 
      invariant 0 <= i <= a.Length/2
      invariant (forall j :: 0 <= j < i ==> a[j] <= a[2*j+1] && (2*j+2 < a.Length ==> a[j] <= a[2*j+2]))
    {
      if a[i] > a[2*i+1] || (2*i+2 < a.Length && a[i] > a[2*i+2]) {
        return false;
      }
    }
  }
  return true;
}

// Test cases checked statically.
method IsMinHeapTest(){
  // Totally sorted
  var a1:= new int[] [1, 2, 3, 4, 5, 6];
  var res1:=IsMinHeap(a1);
  assert res1;

  // Partially sorted
  var a2:= new int[] [2, 4, 3, 5, 10, 15];
  var res2 := IsMinHeap(a2);
  assert res2;

  // Not partially sorted
  var a3:= new int[] [2, 10, 4, 5, 3, 15];
  var res3 := IsMinHeap(a3);
  assert !res3;
}

