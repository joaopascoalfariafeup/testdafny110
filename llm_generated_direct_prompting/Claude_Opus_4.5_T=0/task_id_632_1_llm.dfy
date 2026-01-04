// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.

ghost function NonZeroElements(s: seq<int>): seq<int>
{
    if |s| == 0 then []
    else if s[|s|-1] != 0 then NonZeroElements(s[..|s|-1]) + [s[|s|-1]]
    else NonZeroElements(s[..|s|-1])
}

ghost function CountZeroes(s: seq<int>): nat
{
    if |s| == 0 then 0
    else if s[|s|-1] == 0 then 1 + CountZeroes(s[..|s|-1])
    else CountZeroes(s[..|s|-1])
}

ghost predicate AllZeroes(s: seq<int>)
{
    forall k :: 0 <= k < |s| ==> s[k] == 0
}

method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz <= a.Length
    ensures forall k :: 0 <= k < nz ==> a[k] != 0
    ensures forall k :: nz <= k < a.Length ==> a[k] == 0
    ensures NonZeroElements(a[..]) == NonZeroElements(old(a[..]))
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant nz <= i
        invariant forall k :: 0 <= k < nz ==> a[k] != 0
        invariant forall k :: nz <= k < i ==> a[k] == 0
        invariant NonZeroElements(a[..i]) == NonZeroElements(old(a[..i]))
        invariant a[i..] == old(a[i..])
    {
        if a[i] != 0 {
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            nz := nz + 1; // increment number of non-zero elements
        }
    }    
}




method {:fuel NonZeroElements,5} MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    var nz1 := MoveZeroesToEnd(a1);
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    var nz2 := MoveZeroesToEnd(a2);
    assert nz2 == 2 && a2[..] == [1, 1, 0, 0];
}
