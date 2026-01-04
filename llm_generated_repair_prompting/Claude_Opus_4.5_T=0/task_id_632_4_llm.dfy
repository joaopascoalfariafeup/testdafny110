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

lemma CountNonZeroConcat(s1: seq<int>, s2: seq<int>)
    ensures CountNonZero(s1 + s2) == CountNonZero(s1) + CountNonZero(s2)
{
    if |s2| == 0 {
        assert s1 + s2 == s1;
    } else {
        assert (s1 + s2)[..|s1 + s2|-1] == s1 + s2[..|s2|-1];
        CountNonZeroConcat(s1, s2[..|s2|-1]);
    }
}

lemma AllZeroNonZeroElements(s: seq<int>)
    requires AllZero(s)
    ensures NonZeroElements(s) == []
{
    if |s| > 0 {
        AllZeroNonZeroElements(s[..|s|-1]);
    }
}

lemma AllNonZeroElements(s: seq<int>)
    requires AllNonZero(s)
    ensures NonZeroElements(s) == s
{
    if |s| > 0 {
        AllNonZeroElements(s[..|s|-1]);
    }
}

method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz <= a.Length
    ensures AllNonZero(a[..nz])
    ensures AllZero(a[nz..])
    ensures NonZeroElements(a[..]) == NonZeroElements(old(a[..]))
    ensures nz == CountNonZero(old(a[..]))
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant nz <= i
        invariant AllNonZero(a[..nz])
        invariant AllZero(a[nz..i])
        invariant a[..nz] == NonZeroElements(old(a[..i]))
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant nz == CountNonZero(old(a[..i]))
    {
        assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
        if a[i] != 0 {
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            assert a[..nz+1] == a[..nz] + [a[nz]];
            nz := nz + 1; // increment number of non-zero elements
        }
    }
    assert a[..a.Length] == a[..];
    assert old(a[..a.Length]) == old(a[..]);
    AllNonZeroElements(a[..nz]);
    NonZeroElementsConcat(a[..nz], a[nz..]);
    assert a[..] == a[..nz] + a[nz..];
    AllZeroNonZeroElements(a[nz..]);
}

method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    assert a1[..] == [1, 0, 0, 3];
    assert NonZeroElements([1, 0, 0, 3]) == [1, 3];
    assert CountNonZero([1, 0, 0, 3]) == 2;
    var nz1 := MoveZeroesToEnd(a1);
    assert NonZeroElements(a1[..]) == [1, 3];
    assert AllNonZero(a1[..nz1]);
    assert AllZero(a1[nz1..]);
    assert nz1 == 2;
    assert a1[..nz1] == [1, 3];
    assert a1[0] == 1 && a1[1] == 3;
    assert a1[2] == 0 && a1[3] == 0;
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    assert a2[..] == [0, 1, 0, 1];
    assert NonZeroElements([0, 1, 0, 1]) == [1, 1];
    assert CountNonZero([0, 1, 0, 1]) == 2;
    var nz2 := MoveZeroesToEnd(a2);
    assert NonZeroElements(a2[..]) == [1, 1];
    assert AllNonZero(a2[..nz2]);
    assert AllZero(a2[nz2..]);
    assert nz2 == 2;
    assert a2[..nz2] == [1, 1];
    assert a2[0] == 1 && a2[1] == 1;
    assert a2[2] == 0 && a2[3] == 0;
    assert nz2 == 2 && a2[..] == [1, 1, 0, 0];
}
