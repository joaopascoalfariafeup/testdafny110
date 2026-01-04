// Obtains the set of elements (without duplicates) shared between two arrays. 
function SeqToSet<T>(s: seq<T>): set<T>
{
  set x | x in s :: x
}

lemma SeqToSetAppend<T>(s: seq<T>, x: T)
  ensures SeqToSet(s + [x]) == SeqToSet(s) + {x}
{
  assert forall y :: y in SeqToSet(s + [x]) <==> y in (SeqToSet(s) + {x}) by
  {
    intro y;
    assert (y in SeqToSet(s + [x])) <==> (y in (s + [x]));
    assert (y in SeqToSet(s)) <==> (y in s);
    if y in s {
      assert y in s + [x];
      assert y in SeqToSet(s);
      assert y in SeqToSet(s) + {x};
    } else {
      if y == x {
        assert y in s + [x];
        assert y in {x};
        assert y in SeqToSet(s) + {x};
      } else {
        assert !(y in s + [x]);
        assert !(y in SeqToSet(s));
        assert !(y in {x});
        assert !(y in SeqToSet(s) + {x});
      }
    }
  };
}

method SharedElements<T(==)>(a: array<T>, b: array<T>) returns (result: set<T>)
  ensures result == SeqToSet(a[..]) * SeqToSet(b[..])
{
  result := {};
  for i := 0 to a.Length // loop through the first array
    invariant 0 <= i <= a.Length
    invariant result == SeqToSet(a[..i]) * SeqToSet(b[..])
  {
    if a[i] !in result && a[i] in b[..] {
      assert result == SeqToSet(a[..i]) * SeqToSet(b[..]);
      assert a[i] !in SeqToSet(a[..i]) by {
        // since a[i] in b[..], a[i] !in result implies a[i] !in SeqToSet(a[..i])
        if a[i] in SeqToSet(a[..i]) {
          assert a[i] in SeqToSet(b[..]);
          assert a[i] in SeqToSet(a[..i]) * SeqToSet(b[..]);
          assert a[i] in result;
        }
      }
      result := result + {a[i]};
      SeqToSetAppend(a[..i], a[i]);
      assert SeqToSet(a[..i + 1]) == SeqToSet(a[..i]) + {a[i]};
      assert result == SeqToSet(a[..i + 1]) * SeqToSet(b[..]) by {
        assert a[i] in SeqToSet(b[..]);
        assert a[i] !in SeqToSet(a[..i]);
        assert forall y :: y in result <==> y in (SeqToSet(a[..i + 1]) * SeqToSet(b[..])) by
        {
          intro y;
          if y == a[i] {
            assert y in {a[i]};
            assert y in result;
            assert y in SeqToSet(a[..i + 1]);
            assert y in SeqToSet(b[..]);
            assert y in SeqToSet(a[..i + 1]) * SeqToSet(b[..]);
          } else {
            assert (y in (result + {a[i]})) <==> (y in result);
            assert (y in (SeqToSet(a[..i]) + {a[i]})) <==> (y in SeqToSet(a[..i]));
            assert (y in (SeqToSet(a[..i]) * SeqToSet(b[..]))) <==> (y in result);
          }
        };
      }
    } else {
      SeqToSetAppend(a[..i], a[i]);
      assert SeqToSet(a[..i + 1]) == SeqToSet(a[..i]) + {a[i]};
      if a[i] !in b[..] {
        assert a[i] !in SeqToSet(b[..]);
        assert SeqToSet(a[..i + 1]) * SeqToSet(b[..]) == SeqToSet(a[..i]) * SeqToSet(b[..]) by {
          assert forall y :: y in (SeqToSet(a[..i + 1]) * SeqToSet(b[..])) <==> y in (SeqToSet(a[..i]) * SeqToSet(b[..])) by
          {
            intro y;
            if y in SeqToSet(b[..]) {
              assert y in SeqToSet(a[..i + 1]) <==> y in (SeqToSet(a[..i]) + {a[i]});
              if y == a[i] {
                assert y !in SeqToSet(b[..]);
              }
            }
          };
        }
        assert result == SeqToSet(a[..i + 1]) * SeqToSet(b[..]);
      } else if a[i] in result {
        assert a[i] in SeqToSet(a[..i]) * SeqToSet(b[..]);
        assert a[i] in SeqToSet(a[..i]);
        assert SeqToSet(a[..i + 1]) * SeqToSet(b[..]) == SeqToSet(a[..i]) * SeqToSet(b[..]) by {
          assert forall y :: y in (SeqToSet(a[..i + 1]) * SeqToSet(b[..])) <==> y in (SeqToSet(a[..i]) * SeqToSet(b[..])) by
          {
            intro y;
            if y in SeqToSet(b[..]) {
              assert y in SeqToSet(a[..i + 1]) <==> y in (SeqToSet(a[..i]) + {a[i]});
            }
          };
        }
        assert result == SeqToSet(a[..i + 1]) * SeqToSet(b[..]);
      } else {
        assert result == SeqToSet(a[..i]) * SeqToSet(b[..]);
        assert a[i] in SeqToSet(b[..]);
        assert a[i] !in result;
        // then necessarily a[i] !in SeqToSet(a[..i]) (as in the then-branch proof), contradicting a[i] in result check,
        // but intersection still unchanged since a[i] not in SeqToSet(a[..i])
        assert a[i] !in SeqToSet(a[..i]) by {
          if a[i] in SeqToSet(a[..i]) {
            assert a[i] in SeqToSet(b[..]);
            assert a[i] in SeqToSet(a[..i]) * SeqToSet(b[..]);
            assert a[i] in result;
          }
        }
        assert SeqToSet(a[..i + 1]) * SeqToSet(b[..]) == SeqToSet(a[..i]) * SeqToSet(b[..]) by {
          assert forall y :: y in (SeqToSet(a[..i + 1]) * SeqToSet(b[..])) <==> y in (SeqToSet(a[..i]) * SeqToSet(b[..])) by
          {
            intro y;
            if y == a[i] {
              assert !(y in SeqToSet(a[..i]));
              assert y in SeqToSet(a[..i + 1]) <==> y in (SeqToSet(a[..i]) + {a[i]});
            } else {
              assert y in SeqToSet(a[..i + 1]) <==> y in (SeqToSet(a[..i]) + {a[i]});
              assert (y in (SeqToSet(a[..i]) + {a[i]})) <==> (y in SeqToSet(a[..i]));
            }
          };
        }
        assert result == SeqToSet(a[..i + 1]) * SeqToSet(b[..]);
      }
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
