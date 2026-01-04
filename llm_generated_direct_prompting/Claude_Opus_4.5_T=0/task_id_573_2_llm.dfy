// Difficult example because of the need for auxiliary lemmas.

// Ghost function to compute the product of elements in a set
ghost function SetProduct(s: set<int>): int
{
    if s == {} then 1
    else var x :| x in s; x * SetProduct(s - {x})
}

// Lemma: Adding an element to a set multiplies the product
lemma SetProductAdd(s: set<int>, x: int)
    requires x !in s
    ensures SetProduct(s + {x}) == SetProduct(s) * x
{
    var s' := s + {x};
    assert x in s';
    assert s' - {x} == s;
    SetProductCommutative(s', x);
}

// Lemma: SetProduct is commutative in element selection
lemma SetProductCommutative(s: set<int>, x: int)
    requires x in s
    ensures SetProduct(s) == x * SetProduct(s - {x})
{
    if s == {} {
    } else {
        var y :| y in s && SetProduct(s) == y * SetProduct(s - {y});
        if x == y {
        } else {
            calc {
                SetProduct(s);
                == y * SetProduct(s - {y});
                == { SetProductCommutative(s - {y}, x); }
                   y * (x * SetProduct((s - {y}) - {x}));
                == x * (y * SetProduct((s - {y}) - {x}));
                == { assert (s - {y}) - {x} == (s - {x}) - {y}; }
                   x * (y * SetProduct((s - {x}) - {y}));
                == { SetProductCommutative(s - {x}, y); }
                   x * SetProduct(s - {x});
            }
        }
    }
}

// Lemma: Product of set containing 0 is 0
lemma SetProductZero(s: set<int>)
    requires 0 in s
    ensures SetProduct(s) == 0
{
    SetProductCommutative(s, 0);
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
    ensures exists s: set<int> :: (forall k :: 0 <= k < a.Length ==> a[k] in s) && 
                                  (forall x :: x in s ==> exists k :: 0 <= k < a.Length && a[k] == x) &&
                                  product == SetProduct(s)
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
        invariant forall k :: 0 <= k < i ==> a[k] in seen
        invariant forall x :: x in seen ==> exists k :: 0 <= k < i && a[k] == x
        invariant product == SetProduct(seen)
    {
        if a[i] !in seen {
            SetProductAdd(seen, a[i]);
            seen := seen + {a[i]};
            product := product * a[i];
        }
    }
}

// Lemma for test case 1
lemma Test1Lemma()
    ensures SetProduct({1, 2, 3}) == 6
{
    assert {1, 2, 3} - {3} == {1, 2};
    assert {1, 2} - {2} == {1};
    assert {1} - {1} == {};
    SetProductCommutative({1, 2, 3}, 3);
    SetProductCommutative({1, 2}, 2);
    SetProductCommutative({1}, 1);
}

// Lemma for test case 2
lemma Test2Lemma()
    ensures SetProduct({7, 8, 9, 0, 1}) == 0
{
    SetProductZero({7, 8, 9, 0, 1});
}

// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 3 && a1[3] == 2 && a1[4] == 3;
  ghost var s1: set<int> :| (forall k :: 0 <= k < a1.Length ==> a1[k] in s1) && 
                            (forall x :: x in s1 ==> exists k :: 0 <= k < a1.Length && a1[k] == x) &&
                            out1 == SetProduct(s1);
  assert 1 in s1 && 2 in s1 && 3 in s1;
  assert forall x :: x in s1 ==> x == 1 || x == 2 || x == 3;
  assert s1 == {1, 2, 3};
  Test1Lemma();
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert a2[0] == 7 && a2[1] == 8 && a2[2] == 9 && a2[3] == 0 && a2[4] == 1 && a2[5] == 1;
  ghost var s2: set<int> :| (forall k :: 0 <= k < a2.Length ==> a2[k] in s2) && 
                            (forall x :: x in s2 ==> exists k :: 0 <= k < a2.Length && a2[k] == x) &&
                            out2 == SetProduct(s2);
  assert 0 in s2;
  Test2Lemma();
  SetProductZero(s2);
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
