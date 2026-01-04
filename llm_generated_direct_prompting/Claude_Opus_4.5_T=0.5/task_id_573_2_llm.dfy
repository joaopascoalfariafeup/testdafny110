// Difficult example because of the need for auxiliary lemmas.

// Ghost function to compute the product of a set of integers
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
    calc {
        SetProduct(s');
        == { assert x in s'; }
        x * SetProduct(s' - {x});
        == x * SetProduct(s);
        == SetProduct(s) * x;
    }
}

// Lemma: Product of empty set is 1
lemma SetProductEmpty()
    ensures SetProduct({}) == 1
{
}

// Lemma: Product of {1, 2, 3} is 6
lemma SetProduct123()
    ensures SetProduct({1, 2, 3}) == 6
{
    SetProductEmpty();
    SetProductAdd({}, 1);
    assert SetProduct({1}) == 1;
    SetProductAdd({1}, 2);
    assert SetProduct({1, 2}) == 2;
    SetProductAdd({1, 2}, 3);
    assert SetProduct({1, 2, 3}) == 6;
}

// Lemma: Product containing 0 is 0
lemma SetProductZero(s: set<int>)
    requires 0 in s
    ensures SetProduct(s) == 0
{
    if s == {0} {
        assert SetProduct({0}) == 0 * SetProduct({}) == 0;
    } else {
        var x :| x in s;
        if x == 0 {
            assert SetProduct(s) == 0 * SetProduct(s - {0}) == 0;
        } else {
            assert 0 in (s - {x});
            SetProductZero(s - {x});
            assert SetProduct(s - {x}) == 0;
            assert SetProduct(s) == x * SetProduct(s - {x}) == x * 0 == 0;
        }
    }
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
  SetProduct123();
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  var s2 := set i | 0 <= i < a2.Length :: a2[i];
  assert 0 in s2;
  SetProductZero(s2);
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
