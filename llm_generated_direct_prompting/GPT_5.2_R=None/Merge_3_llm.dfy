
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate SortedArr(a: array<int>)
  reads a
{
  Sorted(a[..])
}

ghost predicate MultisetEq(s: seq<int>, t: seq<int>)
{
  multiset(s) == multiset(t)
}

ghost function PrefixLeqAll(x: seq<int>, y: seq<int>): bool
{
  forall p, q :: 0 <= p < |x| && 0 <= q < |y| ==> x[p] <= y[q]
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires SortedArr(a)
  requires SortedArr(b)
  ensures c.Length == a.Length + b.Length
  ensures SortedArr(c)
  ensures MultisetEq(c[..], a[..] + b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j <= c.Length
      invariant c[..i+j] == if i + j == 0 then [] else c[..i+j]
      invariant MultisetEq(c[..i+j], a[..i] + b[..j])
      invariant Sorted(c[..i+j])
      invariant i < a.Length ==> PrefixLeqAll(c[..i+j], a[i..])
      invariant j < b.Length ==> PrefixLeqAll(c[..i+j], b[j..])
      decreases (a.Length - i) + (b.Length - j)
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

