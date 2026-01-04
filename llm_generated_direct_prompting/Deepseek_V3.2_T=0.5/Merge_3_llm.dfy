
// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires a != null && b != null
  requires forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
  requires forall k :: 0 <= k < b.Length - 1 ==> b[k] <= b[k+1]
  ensures c != null
  ensures c.Length == a.Length + b.Length
  ensures forall k :: 0 <= k < c.Length - 1 ==> c[k] <= c[k+1]
  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j == |c[..i+j]|
      invariant forall k :: 0 <= k < i+j - 1 ==> c[k] <= c[k+1]
      invariant multiset(c[..i+j]) == multiset(a[..i]) + multiset(b[..j])
      invariant i < a.Length ==> (j == b.Length || a[i] <= b[j]) || (j < b.Length && b[j] < a[i])
      invariant j < b.Length ==> (i == a.Length || b[j] <= a[i]) || (i < a.Length && a[i] < b[j])
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];
            i := i + 1;
        } 
        else {
            c[i + j] := b[j];
            j := j + 1;
        }
    }

}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

