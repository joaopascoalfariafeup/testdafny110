// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.

// Helper ghost function to extract non-zero elements in order
ghost function NonZeroSeq(s: seq<int>): seq<int>
  ensures |NonZeroSeq(s)| <= |s|
  ensures forall i :: 0 <= i < |NonZeroSeq(s)| ==> NonZeroSeq(s)[i] != 0
  ensures forall i, j :: 0 <= i < j < |s| && s[i] != 0 && s[j] != 0 ==> 
    exists k, l :: 0 <= k < l < |NonZeroSeq(s)| && NonZeroSeq(s)[k] == s[i] && NonZeroSeq(s)[l] == s[j]
{
  if |s| == 0 then []
  else if s[0] != 0 then [s[0]] + NonZeroSeq(s[1..])
  else NonZeroSeq(s[1..])
}

// Helper lemma to prove NonZeroSeq preserves order when swapping
lemma NonZeroSeqSwapLemma(s: seq<int>, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] != 0 && s[j] != 0
  ensures NonZeroSeq(s[i := s[j]][j := s[i]]) == NonZeroSeq(s)
{
  // This lemma helps prove that swapping two non-zero elements doesn't change NonZeroSeq
  // The proof relies on the fact that NonZeroSeq only cares about order, not positions
  // Since both elements are non-zero and we're swapping them, the sequence of non-zero elements remains the same
  // We'll prove this by induction on the sequence
  if |s| == 0 {
    // trivial case
  } else {
    // Recursive case: compare the first element
    if s[0] != 0 {
      // Both sequences start with the same non-zero element
      // Need to show the rest is equal
      calc {
        NonZeroSeq(s[i := s[j]][j := s[i]]);
        == // by definition
        [s[i := s[j]][j := s[i]][0]] + NonZeroSeq(s[i := s[j]][j := s[i]][1..]);
        == // since 0 != i and 0 != j when i,j > 0
        [s[0]] + NonZeroSeq(s[1..][(i-1) := s[j]][(j-1) := s[i]]);
        == // by induction hypothesis
        [s[0]] + NonZeroSeq(s[1..]);
        == // by definition
        NonZeroSeq(s);
      }
    } else {
      // Both sequences skip the zero at position 0
      calc {
        NonZeroSeq(s[i := s[j]][j := s[i]]);
        == // by definition
        NonZeroSeq(s[i := s[j]][j := s[i]][1..]);
        == // since 0 != i and 0 != j when i,j > 0
        NonZeroSeq(s[1..][(i-1) := s[j]][(j-1) := s[i]]);
        == // by induction hypothesis
        NonZeroSeq(s[1..]);
        == // by definition
        NonZeroSeq(s);
      }
    }
  }
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
        invariant NonZeroSeq(a[..i]) == NonZeroSeq(old(a[..i]))
        invariant NonZeroSeq(a[..]) == NonZeroSeq(old(a[..]))
    {
        if a[i] != 0 {
            if nz < i {
                // Before swap, prove that swapping maintains NonZeroSeq
                // The element at position i is non-zero and will be moved to position nz
                // All elements between nz and i-1 are zero (from invariant)
                // So swapping doesn't change the relative order of non-zero elements
                NonZeroSeqSwapLemma(a[..], nz, i);
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            nz := nz + 1; // increment number of non-zero elements
        }
    }    
}

method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    // Helper assertions to establish initial state
    assert a1[..] == [1, 0, 0, 3];
    // Prove NonZeroSeq for a1
    calc {
      NonZeroSeq(a1[..]);
      == NonZeroSeq([1, 0, 0, 3]);
      == [1] + NonZeroSeq([0, 0, 3]);
      == [1] + NonZeroSeq([0, 3]);
      == [1] + NonZeroSeq([3]);
      == [1] + [3];
      == [1, 3];
    }
    assert NonZeroSeq(a1[..]) == [1, 3];
    var nz1 := MoveZeroesToEnd(a1);
    // Additional helper assertions
    assert a1[0] == 1 && a1[1] == 3 && a1[2] == 0 && a1[3] == 0;
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
    assert NonZeroSeq(a1[..]) == [1, 3];
 
    var a2 := new int[] [0, 1, 0, 1];
    // Helper assertions to establish initial state
    assert a2[..] == [0, 1, 0, 1];
    // Prove NonZeroSeq for a2
    calc {
      NonZeroSeq(a2[..]);
      == NonZeroSeq([0, 1, 0, 1]);
      == NonZeroSeq([1, 0, 1]);
      == [1] + NonZeroSeq([0, 1]);
      == [1] + NonZeroSeq([1]);
      == [1] + [1];
      == [1, 1];
    }
    assert NonZeroSeq(a2[..]) == [1, 1];
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
    assert NonZeroSeq(a2[..]) == [1, 1];
}


