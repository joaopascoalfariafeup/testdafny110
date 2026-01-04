// Ghost helper: filter a sequence, preserving order
ghost function SeqFilter<T>(s: seq<T>, p: T -> bool): seq<T>
{
  if |s| == 0 then []
  else
    var t := SeqFilter(s[..|s|-1], p);
    if p(s[|s|-1]) then t + [s[|s|-1]] else t
}

// Useful lemma: filtering distributes over concatenation
lemma SeqFilterConcat<T>(s: seq<T>, t: seq<T>, p: T -> bool)
  ensures SeqFilter(s + t, p) == SeqFilter(s, p) + SeqFilter(t, p)
{
  if |t| == 0 {
    // SeqFilter(s + []) == SeqFilter(s) and SeqFilter([]) == []
  } else {
    // peel off the last element of t
    SeqFilterConcat(s, t[..|t|-1], p);

    // make the concatenation shape explicit
    assert t == t[..|t|-1] + [t[|t|-1]];
    assert s + t == (s + t[..|t|-1]) + [t[|t|-1]];

    // unfold SeqFilter on (s + t) and use IH
    // (the following assertion is the key step the verifier needs)
    assert SeqFilter((s + t[..|t|-1]) + [t[|t|-1]], p)
        == SeqFilter(s + t[..|t|-1], p) + (if p(t[|t|-1]) then [t[|t|-1]] else []);

    // also unfold on the right side
    assert SeqFilter(t, p)
        == SeqFilter(t[..|t|-1], p) + (if p(t[|t|-1]) then [t[|t|-1]] else []);

    // finish by rewriting with IH
  }
}

// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.
method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz <= a.Length
    ensures forall i :: 0 <= i < nz ==> a[i] != 0
    ensures forall i :: nz <= i < a.Length ==> a[i] == 0
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures a[..nz] == SeqFilter(old(a[..]), x => x != 0)
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant 0 <= nz <= i <= a.Length
        invariant forall k :: 0 <= k < nz ==> a[k] != 0
        invariant multiset(a[..]) == multiset(old(a[..]))
        // stronger: processed prefix has all the non-zeros (in order), and the rest up to i are zeros
        invariant a[..nz] == SeqFilter(old(a[..i]), x => x != 0)
        invariant forall k :: nz <= k < i ==> a[k] == 0
    {
        if a[i] != 0 {
            if nz < i {
                // position nz is in [nz, i), hence is 0 by the invariant
                assert a[nz] == 0;
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
                // after the swap, position i contains the old a[nz], which is 0
                assert a[i] == 0;
            }
            // update filtered-prefix equality for i+1 (non-zero case)
            assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
            SeqFilterConcat(old(a[..i]), [old(a[i])], x => x != 0);
            assert SeqFilter(old(a[..i+1]), x => x != 0)
                 == SeqFilter(old(a[..i]), x => x != 0) + (if old(a[i]) != 0 then [old(a[i])] else []);
            nz := nz + 1; // increment number of non-zero elements
        } else {
            // update filtered-prefix equality for i+1 (zero case)
            assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
            SeqFilterConcat(old(a[..i]), [old(a[i])], x => x != 0);
            assert SeqFilter(old(a[..i+1]), x => x != 0)
                 == SeqFilter(old(a[..i]), x => x != 0) + (if old(a[i]) != 0 then [old(a[i])] else []);
        }
    }
    // At loop end, i == a.Length, so the invariant gives the needed facts
    assert forall k :: nz <= k < a.Length ==> a[k] == 0;
    assert a[..nz] == SeqFilter(old(a[..a.Length]), x => x != 0);
    assert old(a[..a.Length]) == old(a[..]);
    assert a[..nz] == SeqFilter(old(a[..]), x => x != 0);
}

method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    assert a1[..] == [1, 0, 0, 3];
    var nz1 := MoveZeroesToEnd(a1);
    assert nz1 == 2;
    assert a1[..] == [1, 3, 0, 0];
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    assert a2[..] == [0, 1, 0, 1];
    var nz2 := MoveZeroesToEnd(a2);
    assert nz2 == 2;
    assert a2[..] == [1, 1, 0, 0];
    assert nz2 == 2 && a2[..] == [1, 1, 0, 0];
}
