// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.

function FilterNonZero(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if s[|s|-1] == 0 then FilterNonZero(s[..|s|-1])
  else FilterNonZero(s[..|s|-1]) + [s[|s|-1]]
}

lemma FilterNonZeroSnoc(s: seq<int>, x: int)
  ensures FilterNonZero(s + [x]) == (if x == 0 then FilterNonZero(s) else FilterNonZero(s) + [x])
{
  if |s| == 0 {
  } else {
    FilterNonZeroSnoc(s[..|s|-1], s[|s|-1]);
  }
}

method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz == |FilterNonZero(old(a[..]))|
    ensures a[..nz] == FilterNonZero(old(a[..]))
    ensures forall k :: nz <= k < a.Length ==> a[k] == 0
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
      invariant 0 <= i <= a.Length
      invariant 0 <= nz <= i
      invariant a[..nz] == FilterNonZero(old(a[..i]))
      invariant forall k :: nz <= k < i ==> a[k] == 0
      invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
    {
        if a[i] != 0 {
            if nz < i {
                assert a[nz] == 0;
                assert a[i] == old(a[i]);
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
                assert a[nz] == old(a[i]);
                assert a[i] == 0;
            } else {
                assert a[i] == old(a[i]);
            }

            FilterNonZeroSnoc(old(a[..i]), old(a[i]));
            assert FilterNonZero(old(a[..i+1])) == FilterNonZero(old(a[..i])) + [old(a[i])];

            assert a[..nz+1] == a[..nz] + [a[nz]];
            assert a[..nz+1] == FilterNonZero(old(a[..i+1]));

            nz := nz + 1; // increment number of non-zero elements
        } else {
            assert a[i] == old(a[i]);
            FilterNonZeroSnoc(old(a[..i]), old(a[i]));
            assert FilterNonZero(old(a[..i+1])) == FilterNonZero(old(a[..i]));
            assert a[..nz] == FilterNonZero(old(a[..i+1]));
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
