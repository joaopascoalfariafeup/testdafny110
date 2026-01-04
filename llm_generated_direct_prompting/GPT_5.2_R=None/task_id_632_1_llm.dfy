// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.
method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz == |seq k | 0 <= k < a.Length && old(a[k]) != 0 :: old(a[k])|
    ensures a[..nz] == seq k | 0 <= k < a.Length && old(a[k]) != 0 :: old(a[k])
    ensures forall k :: nz <= k < a.Length ==> a[k] == 0
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant 0 <= nz <= i <= a.Length
        invariant a[..nz] == seq k | 0 <= k < i && old(a[k]) != 0 :: old(a[k])
        invariant forall k :: nz <= k < i ==> a[k] == 0
        invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
    {
        if a[i] != 0 {
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            nz := nz + 1; // increment number of non-zero elements
        }
    }    
}




method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    var nz1 := MoveZeroesToEnd(a1);
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    var nz2 := MoveZeroesToEnd(a2);
    assert nz2 == 2 && a2[..] == [1, 1, 0, 0];
}
