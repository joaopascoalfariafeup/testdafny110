
// Helper predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if sequence c is a merge of sequences a and b
ghost predicate IsMerge(a: seq<int>, b: seq<int>, c: seq<int>)
{
    |c| == |a| + |b| &&
    multiset(c) == multiset(a) + multiset(b)
}

// Helper function to get the multiset of elements in a sequence
ghost function SeqToMultiset(s: seq<int>): multiset<int>
{
    multiset(s)
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
    requires Sorted(a[..])
    requires Sorted(b[..])
    ensures c.Length == a.Length + b.Length
    ensures Sorted(c[..])
    ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant Sorted(c[..i+j])
        invariant multiset(c[..i+j]) == multiset(a[..i]) + multiset(b[..j])
        invariant forall k :: 0 <= k < i + j ==> (forall m :: i <= m < a.Length ==> c[k] <= a[m])
        invariant forall k :: 0 <= k < i + j ==> (forall m :: j <= m < b.Length ==> c[k] <= b[m])
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

