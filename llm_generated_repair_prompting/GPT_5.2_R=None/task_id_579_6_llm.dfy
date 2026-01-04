// Ghost predicate used to avoid repeating set comprehensions
ghost predicate InArray<T>(a: array<T>, x: T)
  reads a
{
  exists i :: 0 <= i < a.Length && a[i] == x
}

ghost predicate NotInArray<T>(a: array<T>, x: T)
  reads a
{
  forall i :: 0 <= i < a.Length ==> a[i] != x
}

// Finite set of elements occurring in the prefix a[..n]
ghost function PrefixElems<T>(a: array<T>, n: nat): set<T>
  requires n <= a.Length
  reads a
{
  set k | 0 <= k < n :: a[k]
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  ensures res <==> InArray(a, x)
{
    res := false;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant res ==> (exists k :: 0 <= k < i && a[k] == x)
      invariant (!res) ==> (forall k :: 0 <= k < i ==> a[k] != x)
    {
        if a[i] == x {
            res := true;
            break;
        }
    }
    // Help Dafny connect the loop invariants (which talk about the prefix)
    // to the full-array ghost predicate InArray.
    if res {
      assert exists k :: 0 <= k < a.Length && a[k] == x;
    } else {
      assert forall k :: 0 <= k < a.Length ==> a[k] != x;
    }
}

// Takes two arrays and returns the set of elements that are in one array
// but not in the other.
// Implemented using array and set operations.
method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  ensures res ==
    (set x | x in PrefixElems(a, a.Length) && NotInArray(b, x)) +
    (set x | x in PrefixElems(b, b.Length) && NotInArray(a, x))
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant only_in_a == (set x | x in PrefixElems(a, i) && NotInArray(b, x))
    {
        var c := contains(b, a[i]);
        if !c {
            only_in_a := only_in_a + {a[i]};
        }
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
      invariant 0 <= i <= b.Length
      invariant only_in_b == (set x | x in PrefixElems(b, i) && NotInArray(a, x))
    {
        var c := contains(a, b[i]);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
        }
    }

    return only_in_a  + only_in_b;
}


// Test cases checked statically by Dafny.
method DissimilarElementsTest(){
    var a1 := new int[] [3, 4, 3, 5, 6];
    var a2 := new int[] [5, 7, 4, 10, 5];

    // Help Dafny with concrete array contents
    assert a1[..] == [3, 4, 3, 5, 6];
    assert a2[..] == [5, 7, 4, 10, 5];

    var res1 := DissimilarElements(a1, a2);
    assert res1 == {3, 6, 7, 10};

    var res2 := DissimilarElements(a1, a1);
    assert res2 == {};

    var a3 := new int[] [];
    assert a3[..] == [];

    var res3 := DissimilarElements(a1, a3);
    assert  res3 == {3, 4, 5, 6};
}
