/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma MultisetSplit<T>(s: seq<T>)
  requires |s| > 0
  ensures multiset(s) == multiset([s[0]]) + multiset(s[1..])
{
  calc {
    multiset(s);
    == { assert s == [s[0]] + s[1..]; }
    multiset([s[0]] + s[1..]);
    == multiset([s[0]]) + multiset(s[1..]);
  }
}

// Stable, ordering-preserving reference for insertion sort: the sorted permutation is unique for ints.
lemma SortedPermutationUnique(s1: seq<T>, s2: seq<T>)
  requires Sorted(s1) && Sorted(s2)
  requires multiset(s1) == multiset(s2)
  ensures s1 == s2
{
  if |s1| == 0 {
    assert |s2| == 0;
  } else {
    assert |s2| == |s1|;
    var v1 := s1[0];
    var v2 := s2[0];

    if v1 < v2 {
      assert multiset(s1)[v1] >= 1;
      assert multiset(s2)[v1] == multiset(s1)[v1];
      assert multiset(s2)[v1] >= 1;
      var k :| 0 <= k < |s2| && s2[k] == v1;
      assert v2 <= s2[k];
      assert v2 <= v1;
      assert false;
    }
    if v2 < v1 {
      assert multiset(s2)[v2] >= 1;
      assert multiset(s1)[v2] == multiset(s2)[v2];
      assert multiset(s1)[v2] >= 1;
      var k :| 0 <= k < |s1| && s1[k] == v2;
      assert v1 <= s1[k];
      assert v1 <= v2;
      assert false;
    }
    assert v1 == v2;

    assert Sorted(s1[1..]);
    assert Sorted(s2[1..]);

    MultisetSplit(s1);
    MultisetSplit(s2);

    calc {
      multiset(s1[1..]);
      == { }
      multiset(s1) - multiset([v1]);
      == { assert multiset(s2) == multiset(s1); }
      multiset(s2) - multiset([v1]);
      == { }
      multiset(s2[1..]);
    }

    SortedPermutationUnique(s1[1..], s2[1..]);
    assert s1[1..] == s2[1..];
    assert s1 == [v1] + s1[1..];
    assert s2 == [v1] + s2[1..];
  }
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i; 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant i <= a.Length
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant Sorted(a[..i])
      {
        a[j-1], a[j] := a[j], a[j-1];
        j := j - 1;
      }
      if i < a.Length {
        assert a[..i+1] == a[..i] + [a[i]];
      }
    }
}

// Pure (ghost) reference sort: use the abstract "sorted permutation is unique" characterization.
ghost function SortSeq(s: seq<T>): seq<T>
  ensures Sorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
  ensures forall t :: Sorted(t) && multiset(t) == multiset(s) ==> t == SortSeq(s)
{
  var r :| Sorted(r) && multiset(r) == multiset(s)
        && (forall t :: Sorted(t) && multiset(t) == multiset(s) ==> t == r);
  r
}

method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8];
    InsertionSort(a);
    assert Sorted(a[..]);
    assert multiset(a[..]) == multiset([9,4,6,3,8]);
    assert Sorted([3,4,6,8,9]);
    assert multiset([3,4,6,8,9]) == multiset([9,4,6,3,8]);
    SortedPermutationUnique(a[..], [3,4,6,8,9]);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    assert a[..] == [2,1,2];
    InsertionSort(a);
    assert Sorted(a[..]);
    assert multiset(a[..]) == multiset([2,1,2]);
    assert Sorted([1,2,2]);
    assert multiset([1,2,2]) == multiset([2,1,2]);
    SortedPermutationUnique(a[..], [1,2,2]);
    assert a[..] ==  [1, 2, 2];
}

