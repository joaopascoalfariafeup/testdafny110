// Takes two arrays and returns the set of elements that are in one array 
// but not in the other.
// Implemented using array and set operations.

function ArrayAsSet<T>(a: array<T>): set<T>
  reads a
{
  set x | exists i :: 0 <= i < a.Length && a[i] == x
}

function PrefixSet<T>(a: array<T>, n: int): set<T>
  requires 0 <= n <= a.Length
  reads a
{
  set x | exists i :: 0 <= i < n && a[i] == x
}

lemma PrefixSetStep<T>(a: array<T>, i: int)
  requires 0 <= i < a.Length
  ensures PrefixSet(a, i + 1) == PrefixSet(a, i) + {a[i]}
{
  assert forall x :: x in PrefixSet(a, i + 1) <==> x in (PrefixSet(a, i) + {a[i]});
}

lemma PrefixSetAll<T>(a: array<T>)
  ensures PrefixSet(a, a.Length) == ArrayAsSet(a)
{
  assert forall x :: x in PrefixSet(a, a.Length) <==> x in ArrayAsSet(a);
}

method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  ensures res == (ArrayAsSet(a) - ArrayAsSet(b)) + (ArrayAsSet(b) - ArrayAsSet(a))
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant only_in_a == PrefixSet(a, i) - ArrayAsSet(b)
    {
        var c := contains(b, a[i]);
        if !c {
            only_in_a := only_in_a + {a[i]};
        }
        if c {
          assert PrefixSet(a, i + 1) == PrefixSet(a, i) + {a[i]};
          assert a[i] in ArrayAsSet(b);
          assert PrefixSet(a, i + 1) - ArrayAsSet(b) == PrefixSet(a, i) - ArrayAsSet(b);
        } else {
          assert PrefixSet(a, i + 1) == PrefixSet(a, i) + {a[i]};
          assert a[i] !in ArrayAsSet(b);
          assert PrefixSet(a, i + 1) - ArrayAsSet(b) == (PrefixSet(a, i) - ArrayAsSet(b)) + {a[i]};
        }
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
      invariant only_in_b == PrefixSet(b, i) - ArrayAsSet(a)
    {
        var c := contains(a, b[i]);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
        }
        if c {
          assert PrefixSet(b, i + 1) == PrefixSet(b, i) + {b[i]};
          assert b[i] in ArrayAsSet(a);
          assert PrefixSet(b, i + 1) - ArrayAsSet(a) == PrefixSet(b, i) - ArrayAsSet(a);
        } else {
          assert PrefixSet(b, i + 1) == PrefixSet(b, i) + {b[i]};
          assert b[i] !in ArrayAsSet(a);
          assert PrefixSet(b, i + 1) - ArrayAsSet(a) == (PrefixSet(b, i) - ArrayAsSet(a)) + {b[i]};
        }
    }

    assert PrefixSet(a, a.Length) == ArrayAsSet(a);
    assert PrefixSet(b, b.Length) == ArrayAsSet(b);

    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  ensures res == (x in ArrayAsSet(a))
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
