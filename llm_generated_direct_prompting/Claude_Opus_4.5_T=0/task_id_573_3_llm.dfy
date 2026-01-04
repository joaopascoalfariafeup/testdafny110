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
                == x * (y * SetProduct((s - {x}) - {y}));
                == { SetProductCommutative(s - {x}, y); }
                   x * SetProduct(s - {x});
            }
        }
    }
}

// Lemma: If 0 is in the set, the product is 0
lemma SetProductZero(s: set<int>)
    requires 0 in s
    ensures SetProduct(s) == 0
{
    SetProductCommutative(s, 0);
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
    ensures product == SetProduct(set i | 0 <= i < a.Length :: a[i])
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
        invariant seen == set j | 0 <= j < i :: a[j]
        invariant product == SetProduct(seen)
    {
        if a[i] !in seen {
            SetProductAdd(seen, a[i]);
            seen := seen + {a[i]};
            product := product * a[i];
        }
    }
}




// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert (set i | 0 <= i < a1.Length :: a1[i]) == {1, 2, 3};
  assert SetProduct({1}) == 1 by {
    assert 1 in {1};
    SetProductCommutative({1}, 1);
  }
  assert SetProduct({1, 2}) == 2 by {
    SetProductAdd({1}, 2);
  }
  assert SetProduct({1, 2, 3}) == 6 by {
    SetProductAdd({1, 2}, 3);
  }
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert (set i | 0 <= i < a2.Length :: a2[i]) == {7, 8, 9, 0, 1};
  assert 0 in {7, 8, 9, 0, 1};
  SetProductZero({7, 8, 9, 0, 1});
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
