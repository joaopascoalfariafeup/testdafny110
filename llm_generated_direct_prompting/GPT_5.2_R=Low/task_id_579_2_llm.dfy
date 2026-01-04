// Takes two arrays and returns the set of elements that are in one array 
// but not in the other.
// Implemented using array and set operations.

function ArrayElements<T>(a: array<T>): set<T>
  reads a
{
  set i | 0 <= i < a.Length :: a[i]
}

lemma {:opaque} FilteredPrefixStep<T>(a: array<T>, bset: set<T>, i: int)
  requires 0 <= i < a.Length
  ensures (set k | 0 <= k < i + 1 && a[k] !in bset :: a[k]) ==
          (set k | 0 <= k < i && a[k] !in bset :: a[k]) + (if a[i] !in bset then {a[i]} else {})
{
  assert forall x ::
    x in (set k | 0 <= k < i + 1 && a[k] !in bset :: a[k])
    <=>
    x in ((set k | 0 <= k < i && a[k] !in bset :: a[k]) + (if a[i] !in bset then {a[i]} else {}));
}

lemma {:opaque} FilteredAllIsDifference<T>(a: array<T>, bset: set<T>)
  ensures (set k | 0 <= k < a.Length && a[k] !in bset :: a[k]) == ArrayElements(a) - bset
{
  assert forall x ::
    x in (set k | 0 <= k < a.Length && a[k] !in bset :: a[k])
    <=>
    x in (ArrayElements(a) - bset);
}

method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  ensures res == (ArrayElements(a) - ArrayElements(b)) + (ArrayElements(b) - ArrayElements(a))
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant only_in_a == (set k | 0 <= k < i && a[k] !in ArrayElements(b) :: a[k])
    {
        var c := contains(b, a[i]);
        assert c <==> a[i] in ArrayElements(b);
        if !c {
            only_in_a := only_in_a + {a[i]};
        }
        FilteredPrefixStep(a, ArrayElements(b), i);
        assert only_in_a ==
          (set k | 0 <= k < i && a[k] !in ArrayElements(b) :: a[k]) +
          (if a[i] !in ArrayElements(b) then {a[i]} else {});
        assert only_in_a == (set k | 0 <= k < i + 1 && a[k] !in ArrayElements(b) :: a[k]);
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
      invariant only_in_b == (set k | 0 <= k < i && b[k] !in ArrayElements(a) :: b[k])
    {
        var c := contains(a, b[i]);
        assert c <==> b[i] in ArrayElements(a);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
        }
        FilteredPrefixStep(b, ArrayElements(a), i);
        assert only_in_b ==
          (set k | 0 <= k < i && b[k] !in ArrayElements(a) :: b[k]) +
          (if b[i] !in ArrayElements(a) then {b[i]} else {});
        assert only_in_b == (set k | 0 <= k < i + 1 && b[k] !in ArrayElements(a) :: b[k]);
    }

    FilteredAllIsDifference(a, ArrayElements(b));
    FilteredAllIsDifference(b, ArrayElements(a));
    assert only_in_a == ArrayElements(a) - ArrayElements(b);
    assert only_in_b == ArrayElements(b) - ArrayElements(a);

    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  ensures res <==> x in ArrayElements(a)
{
    res := false;
    for i := 0 to a.Length
      invariant !res ==> (forall k :: 0 <= k < i ==> a[k] != x)
      invariant res ==> (exists k :: 0 <= k <= i && k < a.Length && a[k] == x)
    {
        if a[i] == x {
            res := true;
            break;
        }
    }
    if res {
      assert exists k :: 0 <= k < a.Length && a[k] == x;
    } else {
      assert forall k :: 0 <= k < a.Length ==> a[k] != x;
      assert !(exists k :: 0 <= k < a.Length && a[k] == x);
    }
    assert (x in ArrayElements(a)) <==> (exists k :: 0 <= k < a.Length && a[k] == x);
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
