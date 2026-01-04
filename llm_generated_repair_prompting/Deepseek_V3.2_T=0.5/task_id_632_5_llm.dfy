// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.

// Helper ghost function to extract non-zero elements in order
ghost function NonZeroSeq(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if s[0] != 0 then [s[0]] + NonZeroSeq(s[1..])
  else NonZeroSeq(s[1..])
}

method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz <= a.Length
    ensures forall i :: 0 <= i < nz ==> a[i] != 0
    ensures forall i :: nz <= i < a.Length ==> a[i] == 0
    ensures multiset(a[..]) == multiset(old(a[..]))
    // Additional postcondition to preserve order of non-zero elements
    ensures NonZeroSeq(a[..]) == NonZeroSeq(old(a[..]))
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant 0 <= nz <= i <= a.Length
        invariant forall k :: 0 <= k < nz ==> a[k] != 0
        invariant forall k :: nz <= k < i ==> a[k] == 0
        invariant multiset(a[..]) == multiset(old(a[..]))
        // Additional invariant to preserve order of non-zero elements
        invariant NonZeroSeq(a[..i]) == NonZeroSeq(old(a[..]))
    {
        if a[i] != 0 {
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
                // After swap, we need to show that the order invariant is maintained
                // The non-zero element at position i (now at position nz) came from position i
                // All previous non-zero elements at positions < nz remain in same relative order
                // We add an assertion to help the verifier
                assert NonZeroSeq(a[..i+1]) == NonZeroSeq(old(a[..]));
            }
            nz := nz + 1; // increment number of non-zero elements
        }
    }    
}

method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    // Helper assertions to establish initial state
    assert a1[..] == [1, 0, 0, 3];
    var nz1 := MoveZeroesToEnd(a1);
    // Additional helper assertions
    assert a1[0] == 1 && a1[1] == 3 && a1[2] == 0 && a1[3] == 0;
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    // Helper assertions to establish initial state
    assert a2[..] == [0, 1, 0, 1];
    var nz2 := MoveZeroesToEnd(a2);
    // Additional helper assertions
    // First verify the postconditions
    assert nz2 == 2;
    assert forall i :: 0 <= i < nz2 ==> a2[i] != 0;
    assert forall i :: nz2 <= i < a2.Length ==> a2[i] == 0;
    // Now check specific positions
    assert a2[0] == 1;
    assert a2[1] == 1;
    assert a2[2] == 0;
    assert a2[3] == 0;
    // Final check
    assert a2[..] == [1, 1, 0, 0];
}

