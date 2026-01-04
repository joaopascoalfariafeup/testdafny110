// Move all zeroes to the end of the array, preserving the order of non-zero elements.
// Returns the number of non-zero elements in the array.

function {:fuel 10} FilterNonZero(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then
    []
  else
    if s[|s|-1] == 0 then
      FilterNonZero(s[..|s|-1])
    else
      FilterNonZero(s[..|s|-1]) + [s[|s|-1]]
}

lemma FilterNonZeroAppend(s: seq<int>, x: int)
  ensures FilterNonZero(s + [x]) == (if x == 0 then FilterNonZero(s) else FilterNonZero(s) + [x])
  decreases |s|
{
  if |s| == 0 {
  } else {
    FilterNonZeroAppend(s[..|s|-1], x);
  }
}

function {:fuel 10} Zeros(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else Zeros(n-1) + [0]
}

lemma ZerosLength(n: nat)
  ensures |Zeros(n)| == n
  decreases n
{
  if n == 0 {
  } else {
    ZerosLength(n-1);
  }
}

lemma AllZeroSeqImpliesZeros(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0
  ensures s == Zeros(|s|)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var p := s[..|s|-1];
    assert forall i :: 0 <= i < |p| ==> p[i] == 0;
    AllZeroSeqImpliesZeros(p);
    ZerosLength(|p|);
    assert Zeros(|s|) == Zeros(|p|) + [0];
  }
}

// Small computation lemmas to help the test assertions
lemma FilterNonZero_Lit_1003()
  ensures FilterNonZero([1,0,0,3]) == [1,3]
{
  calc {
    FilterNonZero([1,0,0,3]);
    == FilterNonZero([1,0,0] + [3]);
    == FilterNonZero([1,0,0]) + [3] by { FilterNonZeroAppend([1,0,0], 3); }
    == FilterNonZero([1,0] + [0]) + [3];
    == FilterNonZero([1,0]) + [3] by { FilterNonZeroAppend([1,0], 0); }
    == FilterNonZero([1] + [0]) + [3];
    == FilterNonZero([1]) + [3] by { FilterNonZeroAppend([1], 0); }
    == FilterNonZero([] + [1]) + [3];
    == (FilterNonZero([]) + [1]) + [3] by { FilterNonZeroAppend([], 1); }
    == ([] + [1]) + [3];
    == [1] + [3];
    == [1,3];
  }
}

lemma FilterNonZero_Lit_0101()
  ensures FilterNonZero([0,1,0,1]) == [1,1]
{
  calc {
    FilterNonZero([0,1,0,1]);
    == FilterNonZero([0,1,0] + [1]);
    == FilterNonZero([0,1,0]) + [1] by { FilterNonZeroAppend([0,1,0], 1); }
    == FilterNonZero([0,1] + [0]) + [1];
    == FilterNonZero([0,1]) + [1] by { FilterNonZeroAppend([0,1], 0); }
    == FilterNonZero([0] + [1]) + [1];
    == (FilterNonZero([0]) + [1]) + [1] by { FilterNonZeroAppend([0], 1); }
    == (FilterNonZero([] + [0]) + [1]) + [1];
    == (FilterNonZero([]) + [1]) + [1] by { FilterNonZeroAppend([], 0); }
    == ([] + [1]) + [1];
    == [1] + [1];
    == [1,1];
  }
}

method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    ensures nz <= a.Length
    ensures nz == |FilterNonZero(old(a[..]))|
    ensures a[..nz] == FilterNonZero(old(a[..]))
    ensures forall k :: nz <= k < a.Length ==> a[k] == 0
    ensures a[nz..] == Zeros(a.Length - nz)
    ensures a[..] == FilterNonZero(old(a[..])) + Zeros(a.Length - nz)
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
      invariant 0 <= nz <= i <= a.Length
      invariant nz == |FilterNonZero(old(a[..i]))|
      invariant a[..nz] == FilterNonZero(old(a[..i]))
      invariant forall k :: nz <= k < i ==> a[k] == 0
      invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
    {
        // Helpful slice fact about the old array prefix at i+1
        assert old(a[..i+1]) == old(a[..i]) + [old(a[i])];
        FilterNonZeroAppend(old(a[..i]), old(a[i]));

        if a[i] != 0 {
            var nz0 := nz;
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            // The non-zero element placed at position nz0 is exactly old(a[i])
            assert a[nz0] == old(a[i]);
            // Prefix grows by appending that element
            assert a[..nz0+1] == a[..nz0] + [a[nz0]];
            nz := nz + 1; // increment number of non-zero elements

            // Connect to FilterNonZero of the old prefix
            assert old(a[i]) != 0;
            assert a[..nz] == FilterNonZero(old(a[..i])) + [old(a[i])];
            assert a[..nz] == FilterNonZero(old(a[..i+1]));
        } else {
            // a[i] == 0, so FilterNonZero does not change when extending the old prefix
            assert old(a[i]) == 0;
            assert a[..nz] == FilterNonZero(old(a[..i]));
            assert a[..nz] == FilterNonZero(old(a[..i+1]));
        }

        assert forall k :: nz <= k < i + 1 ==> a[k] == 0;
    }

    // Help Dafny connect old(a[..a.Length]) with old(a[..])
    assert old(a[..]) == old(a[..a.Length]);
    assert FilterNonZero(old(a[..])) == FilterNonZero(old(a[..a.Length]));

    // Derive concrete sequence form of the all-zero suffix
    assert forall j :: 0 <= j < |a[nz..]| ==> a[nz..][j] == 0;

    AllZeroSeqImpliesZeros(a[nz..]);

    // Whole-array shape
    assert a[..] == a[..nz] + a[nz..];
}

method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    assert a1[..] == [1, 0, 0, 3];
    // concrete helper facts for the postconditions
    FilterNonZero_Lit_1003();
    assert FilterNonZero([1,0,0,3]) == [1,3];
    assert Zeros(2) == [0,0];

    var nz1 := MoveZeroesToEnd(a1);
    assert nz1 == 2 && a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    assert a2[..] == [0, 1, 0, 1];
    // concrete helper facts for the postconditions
    FilterNonZero_Lit_0101();
    assert FilterNonZero([0,1,0,1]) == [1,1];
    assert Zeros(2) == [0,0];

    var nz2 := MoveZeroesToEnd(a2);
    assert nz2 == 2 && a2[..] == [1, 1, 0, 0];
}
