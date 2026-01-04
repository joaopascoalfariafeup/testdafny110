// Obtains the set of elements (without duplicates) shared between two arrays.

function SharedFromPrefix<T(==)>(a: array<T>, b: array<T>, n: int): set<T>
  requires a != null && b != null
  requires 0 <= n <= a.Length
  reads a, b
{
  set x | (exists i:int :: 0 <= i < n && a[i] == x && x in b[..])
}

lemma SharedFromPrefixStep<T(==)>(a: array<T>, b: array<T>, i: int)
  requires a != null && b != null
  requires 0 <= i < a.Length
  ensures SharedFromPrefix(a, b, i + 1) ==
          (if a[i] in b[..] then SharedFromPrefix(a, b, i) + {a[i]} else SharedFromPrefix(a, b, i))
{
  if a[i] in b[..] {
    forall x:T
      ensures x in SharedFromPrefix(a, b, i + 1) <==> x in (SharedFromPrefix(a, b, i) + {a[i]})
    {
      // unfold SharedFromPrefix at i+1
      assert x in SharedFromPrefix(a, b, i + 1) <==>
             (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]);

      // split witness k=i vs k<i
      assert (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]) <==>
             ((exists k:int :: 0 <= k < i && a[k] == x && x in b[..]) || (a[i] == x && x in b[..]));

      // fold SharedFromPrefix at i
      assert (exists k:int :: 0 <= k < i && a[k] == x && x in b[..]) <==> x in SharedFromPrefix(a, b, i);

      // simplify (a[i] == x && x in b[..]) using a[i] in b[..]
      assert (a[i] == x && x in b[..]) <==> (x == a[i]) by {
        if a[i] == x {
          assert x in b[..]; // from a[i] in b[..] and a[i] == x
        }
      }

      // membership in union-with-singleton
      assert x in (SharedFromPrefix(a, b, i) + {a[i]}) <==>
             (x in SharedFromPrefix(a, b, i) || x == a[i]);
    }
    // extensionality for sets
    assert SharedFromPrefix(a, b, i + 1) == SharedFromPrefix(a, b, i) + {a[i]};
  } else {
    forall x:T
      ensures x in SharedFromPrefix(a, b, i + 1) <==> x in SharedFromPrefix(a, b, i)
    {
      assert x in SharedFromPrefix(a, b, i + 1) <==>
             (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]);

      assert (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]) <==>
             ((exists k:int :: 0 <= k < i && a[k] == x && x in b[..]) || (a[i] == x && x in b[..]));

      // the k=i case is impossible since a[i] !in b[..]
      assert (a[i] == x && x in b[..]) <==> false by {
        if a[i] == x {
          assert x == a[i];
          assert !(x in b[..]); // from a[i] !in b[..] and x==a[i]
        }
      }

      assert ((exists k:int :: 0 <= k < i && a[k] == x && x in b[..]) || (a[i] == x && x in b[..])) <==>
             (exists k:int :: 0 <= k < i && a[k] == x && x in b[..]);

      assert (exists k:int :: 0 <= k < i && a[k] == x && x in b[..]) <==> x in SharedFromPrefix(a, b, i);
    }
    assert SharedFromPrefix(a, b, i + 1) == SharedFromPrefix(a, b, i);
  }
}

lemma SetAddIdempotent<T>(s: set<T>, x: T)
  ensures s + {x} == (if x in s then s else s + {x})
{
  if x in s {
    // show s + {x} == s by extensionality
    assert forall y :: y in (s + {x}) <==> y in s by {
      intro y;
      assert y in (s + {x}) <==> (y in s || y == x);
      if y == x {
        assert y in s; // since x in s
      }
    }
  }
}

method SharedElements<T(==)>(a: array<T>, b: array<T>) returns (result: set<T>)
  requires a != null && b != null
  ensures result == SharedFromPrefix(a, b, a.Length)
{
  result := {};
  for i := 0 to a.Length // loop through the first array
    invariant 0 <= i <= a.Length
    invariant result == SharedFromPrefix(a, b, i)
  {
    ghost var old := result;
    assert old == SharedFromPrefix(a, b, i);

    if a[i] !in result && a[i] in b[..] {
      result := result + {a[i]};
    }

    SharedFromPrefixStep(a, b, i);

    if a[i] in b[..] {
      // SharedFromPrefix(i+1) = SharedFromPrefix(i) + {a[i]}
      assert SharedFromPrefix(a, b, i + 1) == SharedFromPrefix(a, b, i) + {a[i]};

      // result is either old (if already present) or old+{a[i]} (if added)
      if a[i] in old {
        // no update happened (guard had a[i] !in result)
        assert result == old;
        SetAddIdempotent(old, a[i]);
        assert old + {a[i]} == old;
        assert result == SharedFromPrefix(a, b, i) + {a[i]};
      } else {
        // either we added it (if also in b[..]) or it stays absent; here b[..] holds, so we added
        assert result == old + {a[i]};
        assert result == SharedFromPrefix(a, b, i) + {a[i]};
      }
      assert result == SharedFromPrefix(a, b, i + 1);
    } else {
      // SharedFromPrefix(i+1) = SharedFromPrefix(i)
      assert SharedFromPrefix(a, b, i + 1) == SharedFromPrefix(a, b, i);
      // guard requires a[i] in b[..] to update, so result unchanged
      assert result == old;
      assert result == SharedFromPrefix(a, b, i + 1);
    }
  }
}


// Test cases checked statically.
method SharedElementsTest(){
  // arrays with shared elements and no duplicates
  var a1:= new int[] [3, 4, 5, 6];
  var a2:= new int[] [5, 7, 4, 10];
  var res1 := SharedElements(a1, a2);
  assert res1 == {4, 5};

  // arrays with duplicates and shared elements
  var a3:= new int[] [1, 3, 3, 4];
  var a4:= new int[] [4, 4, 3, 7];
  var res2 := SharedElements(a3, a4);
  assert res2 == {3, 4};

  // arrays with no shared elements
  var a5:= new int[] [11, 12, 13];
  var a6:= new int[] [17, 15, 14];
  var res3 := SharedElements(a5, a6);
  assert res3 == {};
}
