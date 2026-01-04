// Takes two arrays and returns the set of elements that are in one array 
// but not in the other.
// Implemented using array and set operations.

predicate InArray<T(==)>(a: array<T>, x: T)
  reads a
{
  exists k:int :: 0 <= k < a.Length && a[k] == x
}

function ArrSet<T(==)>(a: array<T>): set<T>
  reads a
{
  set k:int | 0 <= k < a.Length :: a[k]
}

function OnlyIn<T(==)>(a: array<T>, b: array<T>): set<T>
  reads a, b
{
  set k:int | 0 <= k < a.Length && !InArray(b, a[k]) :: a[k]
}

method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  ensures res == OnlyIn(a, b) + OnlyIn(b, a)
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant only_in_a == (set k:int | 0 <= k < i && !InArray(b, a[k]) :: a[k])
    {
        var c := contains(b, a[i]);
        assert c == InArray(b, a[i]);
        if !c {
            only_in_a := only_in_a + {a[i]};
            assert only_in_a == (set k:int | 0 <= k < i + 1 && !InArray(b, a[k]) :: a[k]);
        } else {
            assert only_in_a == (set k:int | 0 <= k < i + 1 && !InArray(b, a[k]) :: a[k]);
        }
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
      invariant only_in_b == (set k:int | 0 <= k < i && !InArray(a, b[k]) :: b[k])
    {
        var c := contains(a, b[i]);
        assert c == InArray(a, b[i]);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
            assert only_in_b == (set k:int | 0 <= k < i + 1 && !InArray(a, b[k]) :: b[k]);
        } else {
            assert only_in_b == (set k:int | 0 <= k < i + 1 && !InArray(a, b[k]) :: b[k]);
        }
    }

    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  ensures res <==> InArray(a, x)
{
    res := false;
    for i := 0 to a.Length
      invariant res <==> (exists k:int :: 0 <= k < i && a[k] == x)
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
