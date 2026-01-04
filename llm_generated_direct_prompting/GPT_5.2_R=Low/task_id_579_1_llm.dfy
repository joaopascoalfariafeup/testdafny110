// Takes two arrays and returns the set of elements that are in one array 
// but not in the other.
// Implemented using array and set operations.

function ArrSet<T>(a: array<T>): set<T>
  reads a
{
  set i | 0 <= i < a.Length :: a[i]
}

lemma ArrMinusEquiv<T(==)>(a: array<T>, b: array<T>)
  ensures (set j | 0 <= j < a.Length && a[j] !in ArrSet(b) :: a[j]) == ArrSet(a) - ArrSet(b)
{
  assert forall x :: x in (set j | 0 <= j < a.Length && a[j] !in ArrSet(b) :: a[j]) <==> x in (ArrSet(a) - ArrSet(b));
}

method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  ensures res == (ArrSet(a) - ArrSet(b)) + (ArrSet(b) - ArrSet(a))
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant only_in_a == (set j | 0 <= j < i && a[j] !in ArrSet(b) :: a[j])
    {
        var c := contains(b, a[i]);
        if !c {
            only_in_a := only_in_a + {a[i]};
        }
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
      invariant only_in_b == (set j | 0 <= j < i && b[j] !in ArrSet(a) :: b[j])
    {
        var c := contains(a, b[i]);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
        }
    }

    ArrMinusEquiv(a, b);
    ArrMinusEquiv(b, a);
    assert only_in_a == ArrSet(a) - ArrSet(b);
    assert only_in_b == ArrSet(b) - ArrSet(a);

    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  ensures res <==> x in ArrSet(a)
{
    res := false;
    for i := 0 to a.Length
      invariant res ==> (exists j :: 0 <= j < i && a[j] == x)
      invariant !res ==> (forall j :: 0 <= j < i ==> a[j] != x)
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
