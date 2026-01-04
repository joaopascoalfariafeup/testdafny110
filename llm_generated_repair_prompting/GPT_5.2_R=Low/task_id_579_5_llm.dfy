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

// --- Proof helpers ---

lemma InArrayIffInArrSet<T(==)>(a: array<T>, x: T)
  ensures InArray(a, x) <==> x in ArrSet(a)
{
  // InArray(a,x) ==> x in ArrSet(a)
  if InArray(a, x) {
    var k : int :| 0 <= k < a.Length && a[k] == x;
    assert x in ArrSet(a);
  }

  // x in ArrSet(a) ==> InArray(a,x)
  if x in ArrSet(a) {
    var k : int :| 0 <= k < a.Length && a[k] == x;
    assert InArray(a, x);
  }
}

lemma OnlyInAsSetDiff<T(==)>(a: array<T>, b: array<T>)
  ensures OnlyIn(a, b) == ArrSet(a) - ArrSet(b)
{
  // extensionality
  assert forall x:T :: x in OnlyIn(a,b) <==> x in ArrSet(a) - ArrSet(b) by {
    forall x:T
      ensures x in OnlyIn(a,b) <==> x in ArrSet(a) - ArrSet(b)
    {
      // -> direction
      if x in OnlyIn(a,b) {
        var k:int :| 0 <= k < a.Length && !InArray(b, a[k]) && a[k] == x;
        assert x in ArrSet(a);
        InArrayIffInArrSet(b, x);
        assert !(x in ArrSet(b));
        assert x in ArrSet(a) - ArrSet(b);
      }

      // <- direction
      if x in ArrSet(a) - ArrSet(b) {
        var k:int :| 0 <= k < a.Length && a[k] == x;
        InArrayIffInArrSet(b, x);
        assert !(x in ArrSet(b));
        assert !InArray(b, x);
        assert x in OnlyIn(a, b);
      }
    }
  }
}

lemma ArrSetLen0Int(a: array<int>)
  requires a.Length == 0
  ensures ArrSet(a) == {}
{
  assert forall x:int :: x in ArrSet(a) <==> false by {
    forall x:int
      ensures x in ArrSet(a) <==> false
    {
      if x in ArrSet(a) {
        var k:int :| 0 <= k < a.Length && a[k] == x;
        assert false;
      }
    }
  }
}

lemma ArrSetLen5Int(a: array<int>, v0:int, v1:int, v2:int, v3:int, v4:int)
  requires a.Length == 5
  requires a[0] == v0 && a[1] == v1 && a[2] == v2 && a[3] == v3 && a[4] == v4
  ensures ArrSet(a) == {v0, v1, v2, v3, v4}
{
  assert forall x:int :: x in ArrSet(a) <==> x in {v0, v1, v2, v3, v4} by {
    forall x:int
      ensures x in ArrSet(a) <==> x in {v0, v1, v2, v3, v4}
    {
      // -> direction
      if x in ArrSet(a) {
        var k:int :| 0 <= k < a.Length && a[k] == x;
        assert 0 <= k < 5;
        if k == 0 { assert x == v0; }
        else if k == 1 { assert x == v1; }
        else if k == 2 { assert x == v2; }
        else if k == 3 { assert x == v3; }
        else { assert k == 4; assert x == v4; }
        assert x in {v0, v1, v2, v3, v4};
      }

      // <- direction
      if x in {v0, v1, v2, v3, v4} {
        if x == v0 { assert x in ArrSet(a); }
        else if x == v1 { assert x in ArrSet(a); }
        else if x == v2 { assert x in ArrSet(a); }
        else if x == v3 { assert x in ArrSet(a); }
        else { assert x == v4; assert x in ArrSet(a); }
      }
    }
  }
}

method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  ensures res == OnlyIn(a, b) + OnlyIn(b, a)
  ensures res == (ArrSet(a) - ArrSet(b)) + (ArrSet(b) - ArrSet(a))
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
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
      invariant 0 <= i <= b.Length
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

    // connect loop results to set-difference characterization
    assert only_in_a == OnlyIn(a, b);
    assert only_in_b == OnlyIn(b, a);
    OnlyInAsSetDiff(a, b);
    OnlyInAsSetDiff(b, a);

    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  ensures res <==> InArray(a, x)
{
    res := false;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant res ==> InArray(a, x)
      invariant !res ==> (forall k:int :: 0 <= k < i ==> a[k] != x)
    {
        if a[i] == x {
            assert InArray(a, x) by {
              assert 0 <= i < a.Length;
              witness i;
              assert a[i] == x;
            }
            res := true;
            break;
        } else {
            assert a[i] != x;
        }
    }

    if res {
      // res ==> InArray(a,x) already known from the invariant (at loop exit)
      assert InArray(a, x);
    } else {
      assert !InArray(a, x) by {
        if InArray(a, x) {
          var k:int :| 0 <= k < a.Length && a[k] == x;
          // since res is false, the loop did not break, so i == a.Length and the invariant gives all entries != x
          assert forall j:int :: 0 <= j < a.Length ==> a[j] != x;
          assert a[k] != x;
          assert false;
        }
      }
    }
}

// Test cases checked statically by Dafny.
method DissimilarElementsTest(){
    var a1 := new int[] [3, 4, 3, 5, 6];
    var a2 := new int[] [5, 7, 4, 10, 5];

    ArrSetLen5Int(a1, 3, 4, 3, 5, 6);
    ArrSetLen5Int(a2, 5, 7, 4, 10, 5);

    var res1 := DissimilarElements(a1, a2);
    assert res1 == {3, 6, 7, 10};

    var res2 := DissimilarElements(a1, a1);
    assert res2 == {};

    var a3 := new int[] [];
    ArrSetLen0Int(a3);

    var res3 := DissimilarElements(a1, a3);
    assert  res3 == {3, 4, 5, 6};
}
