// Ghost predicate used to avoid repeating set comprehensions
ghost predicate InArray<T(==)>(a: array<T>, x: T)
  reads a
{
  exists i :: 0 <= i < a.Length && a[i] == x
}

ghost predicate NotInArray<T(==)>(a: array<T>, x: T)
  reads a
{
  forall i :: 0 <= i < a.Length ==> a[i] != x
}

// Takes two arrays and returns the set of elements that are in one array
// but not in the other.
// Implemented using array and set operations.
method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  requires a != null && b != null
  ensures res ==
    (set x: T | InArray(a, x) && NotInArray(b, x)) +
    (set x: T | InArray(b, x) && NotInArray(a, x))
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant only_in_a == (set x: T | (exists k :: 0 <= k < i && a[k] == x) && NotInArray(b, x))
    {
        var c := contains(b, a[i]);
        if !c {
            only_in_a := only_in_a + {a[i]};
        }
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
      invariant 0 <= i <= b.Length
      invariant only_in_b == (set x: T | (exists k :: 0 <= k < i && b[k] == x) && NotInArray(a, x))
    {
        var c := contains(a, b[i]);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
        }
    }

    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  requires a != null
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
}


// Test cases checked statically by Dafny.
method DissimilarElementsTest(){
    var a1 := new int[] [3, 4, 3, 5, 6];
    var a2 := new int[] [5, 7, 4, 10, 5];
    var res1 := DissimilarElements(a1, a2);
    assert res1 == {3, 6, 7, 10};

    var res2 := DissimilarElements(a1, a1);
    assert res2 == {};

    var a3 := new int[] [];
    var res3 := DissimilarElements(a1, a3);
    assert  res3 == {3, 4, 5, 6};
}
