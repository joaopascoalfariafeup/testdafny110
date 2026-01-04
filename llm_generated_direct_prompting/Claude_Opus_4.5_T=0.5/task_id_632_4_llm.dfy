// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.

ghost function CountNonZero(s: seq<int>): nat {
    if |s| == 0 then 0
    else (if s[|s|-1] != 0 then 1 else 0) + CountNonZero(s[..|s|-1])
}

ghost function FilterNonZero(s: seq<int>): seq<int> {
    if |s| == 0 then []
    else if s[|s|-1] != 0 then FilterNonZero(s[..|s|-1]) + [s[|s|-1]]
    else FilterNonZero(s[..|s|-1])
}

method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz == CountNonZero(old(a[..]))
    ensures nz <= a.Length
    ensures forall k :: 0 <= k < nz ==> a[k] != 0
    ensures forall k :: nz <= k < a.Length ==> a[k] == 0
    ensures FilterNonZero(a[..]) == FilterNonZero(old(a[..]))
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant nz <= i
        invariant nz == CountNonZero(old(a[..i]))
        invariant forall k :: 0 <= k < nz ==> a[k] != 0
        invariant forall k :: nz <= k < i ==> a[k] == 0
        invariant FilterNonZero(a[..nz]) == FilterNonZero(old(a[..i]))
        invariant a[i..] == old(a[i..])
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if a[i] != 0 {
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
            assert a[..nz+1] == a[..nz] + [a[nz]];
            nz := nz + 1; // increment number of non-zero elements
        } else {
            assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
        }
    }    
    assert a[..] == a[..a.Length];
    assert old(a[..]) == old(a[..a.Length]);
}




method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    var nz1 := MoveZeroesToEnd(a1);
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    var nz2 := MoveZeroesToEnd(a2);
    assert nz2 == 2 && a2[..] == [1, 1, 0, 0];
}
