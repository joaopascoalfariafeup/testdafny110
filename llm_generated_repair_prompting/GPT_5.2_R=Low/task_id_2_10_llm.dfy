// Obtains the set of elements (without duplicates) shared between two arrays.

function SharedFromPrefix<T(==)>(a: array<T>, b: array<T>, n: int): set<T>
  requires 0 <= n <= a.Length
  reads a, b
{
  (set a[..n]) * (set b[..])
}

lemma SetOfSeqPrefixStep<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures set s[..i + 1] == set s[..i] + {s[i]}
{
  assert forall x :: x in set s[..i + 1] <==> x in (set s[..i] + {s[i]}) by
  {
    forall x
      ensures x in set s[..i + 1] <==> x in (set s[..i] + {s[i]})
    {
      // s[..i+1] == s[..i] + [s[i]]
      assert s[..i + 1] == s[..i] + [s[i]];
      // membership in set of concatenation
      assert x in set(s[..i] + [s[i]]) <==> x in set s[..i] || x in set [s[i]];
      assert x in set [s[i]] <==> x == s[i];
      assert x in (set s[..i] + {s[i]}) <==> (x in set s[..i] || x == s[i]);
    }
  }
}

lemma IntersectWithAddSingleton<T>(S: set<T>, B: set<T>, x: T)
  ensures (S + {x}) * B == (S * B) + (if x in B then {x} else {})
{
  assert forall y :: y in ((S + {x}) * B) <==> y in ((S * B) + (if x in B then {x} else {})) by
  {
    forall y
      ensures y in ((S + {x}) * B) <==> y in ((S * B) + (if x in B then {x} else {}))
    {
      if y in ((S + {x}) * B) {
        assert y in (S + {x}) && y in B;
        if y in S {
          assert y in S * B;
          assert y in ((S * B) + (if x in B then {x} else {}));
        } else {
          assert y == x;
          assert x in B;
          assert y in (if x in B then {x} else {});
          assert y in ((S * B) + (if x in B then {x} else {}));
        }
      }

      if y in ((S * B) + (if x in B then {x} else {})) {
        if y in (S * B) {
          assert y in S && y in B;
          assert y in (S + {x});
          assert y in (S + {x}) * B;
        } else {
          assert y in (if x in B then {x} else {});
          assert x in B;
          assert y == x;
          assert y in (S + {x});
          assert y in B;
          assert y in (S + {x}) * B;
        }
      }
    }
  }
}

lemma SharedFromPrefixStep<T(==)>(a: array<T>, b: array<T>, i: int)
  requires 0 <= i < a.Length
  reads a, b
  ensures SharedFromPrefix(a, b, i + 1) ==
          (if a[i] in b[..] then SharedFromPrefix(a, b, i) + {a[i]} else SharedFromPrefix(a, b, i))
{
  var B := set b[..];

  // Expand SharedFromPrefix at i and i+1
  SetOfSeqPrefixStep(a[..], i);
  IntersectWithAddSingleton(set a[..i], B, a[i]);

  // Now rewrite with SharedFromPrefix definition
  assert SharedFromPrefix(a, b, i + 1) == (set a[..i + 1]) * B;
  assert SharedFromPrefix(a, b, i) == (set a[..i]) * B;

  // Use the intersection distribution lemma plus membership equivalence a[i] in b[..] <==> a[i] in set b[..]
  if a[i] in b[..] {
    assert a[i] in B;
    assert (set a[..i + 1]) * B == ((set a[..i]) * B) + {a[i]};
  } else {
    assert !(a[i] in B);
    assert (if a[i] in B then {a[i]} else {}) == {};
    assert (set a[..i + 1]) * B == ((set a[..i]) * B) + {};
    assert ((set a[..i]) * B) + {} == (set a[..i]) * B;
  }
}

lemma SetAddIdempotent<T>(s: set<T>, x: T)
  ensures x in s ==> s + {x} == s
{
  if x in s {
    // (s + {x}) ⊆ s
    assert forall y :: y in s + {x} ==> y in s by {
      forall y
        ensures y in s + {x} ==> y in s
      {
        if y in s + {x} {
          if y in s {
          } else {
            assert y == x;
            assert y in s;
          }
        }
      }
    }
    assert s + {x} <= s;

    // s ⊆ (s + {x})
    assert forall y :: y in s ==> y in s + {x} by {
      forall y
        ensures y in s ==> y in s + {x}
      {
        if y in s {
          assert y in s + {x};
        }
      }
    }
    assert s <= s + {x};

    assert s + {x} == s;
  }
}

method SharedElements<T(==)>(a: array<T>, b: array<T>) returns (result: set<T>)
  ensures result == SharedFromPrefix(a, b, a.Length)
{
  result := {};
  for i := 0 to a.Length // loop through the first array
    invariant 0 <= i <= a.Length
    invariant result == SharedFromPrefix(a, b, i)
  {
    var oldRes := result;
    assert oldRes == SharedFromPrefix(a, b, i);

    if a[i] !in result && a[i] in b[..] {
      result := result + {a[i]};
    }

    SharedFromPrefixStep(a, b, i);

    if a[i] in b[..] {
      assert SharedFromPrefix(a, b, i + 1) == SharedFromPrefix(a, b, i) + {a[i]};

      if a[i] in oldRes {
        assert result == oldRes;
        SetAddIdempotent(oldRes, a[i]);
        assert oldRes + {a[i]} == oldRes;
        assert result == SharedFromPrefix(a, b, i) + {a[i]};
      } else {
        assert result == oldRes + {a[i]};
        assert result == SharedFromPrefix(a, b, i) + {a[i]};
      }
      assert result == SharedFromPrefix(a, b, i + 1);
    } else {
      assert SharedFromPrefix(a, b, i + 1) == SharedFromPrefix(a, b, i);
      assert result == oldRes;
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
