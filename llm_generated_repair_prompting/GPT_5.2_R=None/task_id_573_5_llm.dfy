// Difficult example because of the need for auxiliary lemmas.

ghost function {:fuel 5} SetProduct(s: set<int>): int
  ensures |s| == 0 ==> SetProduct(s) == 1
  decreases |s|
{
  if |s| == 0 then 1
  else
    var x :| x in s;
    x * SetProduct(s - {x})
}

lemma SetMinusSingleton(s: set<int>, x: int)
  requires x in s
  ensures s - {x} + {x} == s
{
}

lemma SetProductEmpty()
  ensures SetProduct({}) == 1
{
}

lemma SetProductAdd(s: set<int>, x: int)
  requires x !in s
  ensures SetProduct(s + {x}) == SetProduct(s) * x
  decreases |s|
{
  if |s| == 0 {
    assert s == {};
    assert s + {x} == {x};
    calc {
      SetProduct(s + {x});
      == SetProduct({x});
      == x * SetProduct({x} - {x});
      == x * SetProduct({});
      == x * 1;
      == 1 * x;
      == SetProduct(s) * x;
    }
  } else {
    var y :| y in s;
    // Use y as the witness when unfolding SetProduct(s+{x})
    assert y in s + {x};
    calc {
      SetProduct(s + {x});
      == y * SetProduct((s + {x}) - {y});
    }

    // Set algebra to rewrite the recursive argument
    assert (s + {x}) - {y} == (s - {y}) + {x};

    // Recurse on a smaller set
    SetProductAdd(s - {y}, x);

    // Unfold SetProduct(s) using y as witness
    assert y in s;
    calc {
      SetProduct(s);
      == y * SetProduct(s - {y});
    }

    // Finish
    calc {
      SetProduct(s + {x});
      == y * SetProduct((s + {x}) - {y});
      == y * SetProduct((s - {y}) + {x});
      == y * (SetProduct(s - {y}) * x);
      == (y * SetProduct(s - {y})) * x;
      == SetProduct(s) * x;
    }
  }
}

method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == SetProduct(set i | 0 <= i < a.Length :: a[i])
{
    product := 1;
    var seen : set<int> := {};

    // establish invariant on entry
    assert SetProduct(seen) == 1;

    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == set j | 0 <= j < i :: a[j]
      invariant product == SetProduct(seen)
    {
        if a[i] !in seen {
            assert a[i] !in (set j | 0 <= j < i :: a[j]);
            // help the verifier relate the updated set to the comprehension at i+1
            assert (set j | 0 <= j < i+1 :: a[j]) == (set j | 0 <= j < i :: a[j]) + {a[i]};

            seen := seen + {a[i]};
            product := product * a[i];

            // use lemma with the pre-state set of elements
            SetProductAdd(set j | 0 <= j < i :: a[j], a[i]);
            assert product == SetProduct(seen);
        }
    }
    assert seen == set i | 0 <= i < a.Length :: a[i];
}

// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  assert a1[..] == [1,2,3,2,3];
  var out1 := UniqueProduct(a1);
  // Help Dafny evaluate the set comprehension concretely
  assert 1 in (set i | 0 <= i < a1.Length :: a1[i]);
  assert 2 in (set i | 0 <= i < a1.Length :: a1[i]);
  assert 3 in (set i | 0 <= i < a1.Length :: a1[i]);
  assert forall v :: v in (set i | 0 <= i < a1.Length :: a1[i]) ==> v == 1 || v == 2 || v == 3;
  assert (set i | 0 <= i < a1.Length :: a1[i]) == {1,2,3};

  assert SetProduct({1,2,3}) == 6;
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  assert a2[..] == [7,8,9,0,1,1];
  var out2 := UniqueProduct(a2);

  assert 0 in (set i | 0 <= i < a2.Length :: a2[i]);
  assert 1 in (set i | 0 <= i < a2.Length :: a2[i]);
  assert 7 in (set i | 0 <= i < a2.Length :: a2[i]);
  assert 8 in (set i | 0 <= i < a2.Length :: a2[i]);
  assert 9 in (set i | 0 <= i < a2.Length :: a2[i]);
  assert forall v :: v in (set i | 0 <= i < a2.Length :: a2[i]) ==> v == 0 || v == 1 || v == 7 || v == 8 || v == 9;
  assert (set i | 0 <= i < a2.Length :: a2[i]) == {0,1,7,8,9};

  assert 0 in {0,1,7,8,9};
  assert SetProduct({0,1,7,8,9}) == 0;
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
