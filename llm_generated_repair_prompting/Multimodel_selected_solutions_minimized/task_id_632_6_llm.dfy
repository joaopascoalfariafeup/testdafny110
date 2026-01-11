
// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.

ghost function {:fuel 5} NonZeroElements(s: seq<int>): seq<int>
{
    if |s| == 0 then []
    else if s[|s|-1] != 0 then NonZeroElements(s[..|s|-1]) + [s[|s|-1]]
    else NonZeroElements(s[..|s|-1])
}

ghost function {:fuel 5} CountNonZero(s: seq<int>): nat
{
    if |s| == 0 then 0
    else if s[|s|-1] != 0 then 1 + CountNonZero(s[..|s|-1])
    else CountNonZero(s[..|s|-1])
}

ghost predicate AllZero(s: seq<int>)
{
    forall k :: 0 <= k < |s| ==> s[k] == 0
}

ghost predicate AllNonZero(s: seq<int>)
{
    forall k :: 0 <= k < |s| ==> s[k] != 0
}

lemma NonZeroElementsOfNonZero(s: seq<int>)
    requires AllNonZero(s)
    ensures NonZeroElements(s) == s
{
    if |s| == 0 {
    } else {
        NonZeroElementsOfNonZero(s[..|s|-1]);
    }
}


lemma NonZeroElementsOfZero(s: seq<int>)
    requires AllZero(s)
    ensures NonZeroElements(s) == []
{
    if |s| == 0 {
    } else {
        NonZeroElementsOfZero(s[..|s|-1]);
    }
}

lemma NonZeroElementsConcat(s1: seq<int>, s2: seq<int>)
    ensures NonZeroElements(s1 + s2) == NonZeroElements(s1) + NonZeroElements(s2)
{
    if |s2| == 0 {
        assert s1 + s2 == s1;
    } else {
        assert (s1 + s2)[..|s1 + s2|-1] == s1 + s2[..|s2|-1];
        NonZeroElementsConcat(s1, s2[..|s2|-1]);
    }
}



method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz <= a.Length
    ensures AllNonZero(a[..nz])
    ensures NonZeroElements(a[..]) == NonZeroElements(old(a[..]))
    ensures nz == CountNonZero(old(a[..]))
{
    ghost var original := a[..];
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant nz <= i
        invariant AllNonZero(a[..nz])
        invariant AllZero(a[nz..i])
        invariant a[..nz] == NonZeroElements(original[..i])
        invariant nz == CountNonZero(original[..i])
        invariant forall j :: i <= j < a.Length ==> a[j] == original[j]
    {
        if a[i] != 0 {
            assert original[..i+1] == original[..i] + [original[i]];
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            nz := nz + 1; // increment number of non-zero elements
        } else {
            assert original[..i+1] == original[..i] + [original[i]];
        }
    }
    assert original[..a.Length] == original;
    NonZeroElementsOfNonZero(a[..nz]);
    NonZeroElementsOfZero(a[nz..]);
    assert a[..] == a[..nz] + a[nz..];
    NonZeroElementsConcat(a[..nz], a[nz..]);
}




method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    assert a1[..] == [1, 0, 0, 3];
    var nz1 := MoveZeroesToEnd(a1);
    assert [1, 0, 0, 3][..3] == [1, 0, 0];
    assert NonZeroElements([1, 0, 0, 3]) == [1, 3];
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    var nz2 := MoveZeroesToEnd(a2);
    assert [0, 1, 0, 1][..3] == [0, 1, 0];
    assert NonZeroElements([0, 1, 0, 1]) == [1, 1];
    assert nz2 == 2 && a2[..] == [1, 1, 0, 0];
}


