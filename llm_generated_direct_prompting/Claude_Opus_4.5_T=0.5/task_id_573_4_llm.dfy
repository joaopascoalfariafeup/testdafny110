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
        // contradiction
    } else {
        var y :| y in s && SetProduct(s) == y * SetProduct(s - {y});
        if x == y {
            // done
        } else {
            var s1 := s - {y};
            var s2 := s - {x};
            var s3 := s - {x} - {y};
            assert s1 - {x} == s3;
            assert s2 - {y} == s3;
            SetProductCommutative(s1, x);
            assert SetProduct(s1) == x * SetProduct(s3);
            SetProductCommutative(s2, y);
            assert SetProduct(s2) == y * SetProduct(s3);
            assert SetProduct(s) == y * SetProduct(s1) == y * x * SetProduct(s3);
            assert x * SetProduct(s2) == x * y * SetProduct(s3);
        }
    }
}

// Lemma for specific set products used in tests
lemma SetProductEmpty()
    ensures SetProduct({}) == 1
{}

lemma SetProductSingleton(x: int)
    ensures SetProduct({x}) == x
{
    assert {x} - {x} == {};
    SetProductCommutative({x}, x);
}

lemma SetProductPair(x: int, y: int)
    requires x != y
    ensures SetProduct({x, y}) == x * y
{
    SetProductSingleton(y);
    assert {x, y} - {x} == {y};
    SetProductCommutative({x, y}, x);
}

lemma SetProductTriple(x: int, y: int, z: int)
    requires x != y && y != z && x != z
    ensures SetProduct({x, y, z}) == x * y * z
{
    SetProductPair(y, z);
    assert {x, y, z} - {x} == {y, z};
    SetProductCommutative({x, y, z}, x);
}

lemma SetProductWithZero(s: set<int>)
    requires 0 in s
    ensures SetProduct(s) == 0
{
    if s == {0} {
        SetProductSingleton(0);
    } else {
        var x :| x in s && SetProduct(s) == x * SetProduct(s - {x});
        if x == 0 {
            // done
        } else {
            assert 0 in s - {x};
            SetProductWithZero(s - {x});
        }
    }
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
    ensures exists seen: set<int> :: (forall k :: 0 <= k < a.Length ==> a[k] in seen) && 
                                      (forall x :: x in seen ==> exists k :: 0 <= k < a.Length && a[k] == x) &&
                                      product == SetProduct(seen)
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




// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 3 && a1[3] == 2 && a1[4] == 3;
  ghost var seen1 : set<int> := {1, 2, 3};
  assert forall k :: 0 <= k < a1.Length ==> a1[k] in seen1;
  assert forall x :: x in seen1 ==> exists k :: 0 <= k < a1.Length && a1[k] == x;
  SetProductTriple(1, 2, 3);
  assert SetProduct(seen1) == 6;
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  ghost var seen2 : set<int> := {7, 8, 9, 0, 1};
  assert a2[3] == 0;
  assert 0 in seen2;
  SetProductWithZero(seen2);
  assert SetProduct(seen2) == 0;
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
