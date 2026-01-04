// Auxiliary predicate that checks if a sequence 's' is sorted.
ghost predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
   requires IsSorted(a[..]) && IsSorted(b[..])
   ensures fresh (c)
   ensures IsSorted(c[..]) 
   ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
       decreases (a.Length - i) + (b.Length - j)
       invariant 0 <= i <= a.Length
       invariant 0 <= j <= b.Length
       invariant IsSorted(c[..i + j])
       invariant multiset(c[..i + j]) == multiset(a[..i]) + multiset(b[..j])
       invariant i < a.Length && i + j > 0 ==> c[i + j - 1] <= a[i]
       invariant j < b.Length && i + j > 0 ==> c[i + j - 1] <= b[j]         
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

    assert a[..a.Length] == a[..]; // helper
    assert b[..b.Length] == b[..]; // helper
    assert c[..c.Length] == c[..]; // helper
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert a[..] == [1, 3, 5]; // helper
    assert b[..]  == [2, 4]; // helper
    assert multiset(c[..]) == multiset{1, 2, 3, 4, 5}; // helper
    assert c[..] == [1, 2, 3, 4, 5];

    var a2: array<int> := new int[] [1, 5, 3];
    var b2: array<int> := new int[] [4, 2];
    //@invalid var c2 := Merge(a2, b); // violates pre-condition
    //@invalid var c3 := Merge(a, b2); // violates pre-condition 
}
