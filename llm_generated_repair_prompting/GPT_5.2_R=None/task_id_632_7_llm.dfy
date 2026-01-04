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
  decreases |t|
{
  if |t| == 0 {
    // s + [] == s and SeqFilter([]) == []
    assert s + t == s;
    assert SeqFilter(t, p) == [];
  } else {
    SeqFilterConcat(s, t[..|t|-1], p);
    assert t == t[..|t|-1] + [t[|t|-1]];
    assert s + t == (s + t[..|t|-1]) + [t[|t|-1]];

    // Expand SeqFilter on the snoc form and use IH
    calc {
      SeqFilter(s + t, p);
      == { }
      SeqFilter((s + t[..|t|-1]) + [t[|t|-1]], p);
      == { }
      SeqFilter(s + t[..|t|-1], p) + (if p(t[|t|-1]) then [t[|t|-1]] else []);
      == { }
      (SeqFilter(s, p) + SeqFilter(t[..|t|-1], p)) + (if p(t[|t|-1]) then [t[|t|-1]] else []);
      == { }
      SeqFilter(s, p) + (SeqFilter(t[..|t|-1], p) + (if p(t[|t|-1]) then [t[|t|-1]] else []));
      == { }
      SeqFilter(s, p) + SeqFilter(t[..|t|-1] + [t[|t|-1]], p);
      == { }
      SeqFilter(s, p) + SeqFilter(t, p);
    }
  }
}

// Single-element specialization (often easier for Dafny than using Concat with [x])
lemma SeqFilterSnoc<T>(s: seq<T>, x: T, p: T -> bool)
  ensures SeqFilter(s + [x], p) == SeqFilter(s, p) + (if p(x) then [x] else [])
{
  // Follows from distributivity over concatenation
  SeqFilterConcat(s, [x], p);
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
    for i := 0 to a.Length
        invariant 0 <= nz <= i <= a.Length
        invariant forall k :: 0 <= k < nz ==> a[k] != 0
        invariant multiset(a[..]) == multiset(old(a[..]))
        // processed prefix has all the non-zeros from old prefix (in order), and the rest up to i are zeros
        invariant a[..nz] == SeqFilter(old(a[..i]), x => x != 0)
        invariant forall k :: nz <= k < i ==> a[k] == 0
    {
        if a[i] != 0 {
            // Since loop invariant says positions [nz..i) are zeros, a[i]!=0 implies nz==i
            // (there cannot be a nonzero at position i if nz<i, because then i is in [nz..i))
            assert nz == i;

            if nz < i {
                assert a[nz] == 0;
                a[nz], a[i] := a[i], a[nz];
                assert a[i] == 0;
            }

            // Prove the filtered-prefix update using the old array element old(a[i])
            // First, relate old prefix i+1 to old prefix i
            assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
            SeqFilterSnoc(old(a[..i]), old(a[i]), x => x != 0);
            assert SeqFilter(old(a[..i+1]), x => x != 0)
                 == SeqFilter(old(a[..i]), x => x != 0) + (if old(a[i]) != 0 then [old(a[i])] else []);

            // Since we established nz==i and we have not modified a[i] before this point, old(a[i])==a[i]
            assert old(a[i]) == a[i];
            assert old(a[i]) != 0;

            // Now re-establish invariant for next iteration (i+1) after incrementing nz
            // Current invariant gives: a[..nz] == SeqFilter(old(a[..i]), ...)
            // After increment: a[..nz+1] == a[..nz] + [a[nz]]
            assert a[..nz+1] == a[..nz] + [a[nz]];
            // and a[nz] is the nonzero moved/kept at position nz
            assert a[nz] == old(a[i]);

            nz := nz + 1;
        } else {
            // zero case: filtered prefix does not grow; nz unchanged
            assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
            SeqFilterSnoc(old(a[..i]), old(a[i]), x => x != 0);
            assert SeqFilter(old(a[..i+1]), x => x != 0)
                 == SeqFilter(old(a[..i]), x => x != 0) + (if old(a[i]) != 0 then [old(a[i])] else []);
            // because current a[i]==0 and we haven't modified a[i] in this iteration, old(a[i])==0
            assert old(a[i]) == a[i];
            assert old(a[i]) == 0;
        }
    }

    // At loop end, i == a.Length, so the invariant gives the needed facts
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
