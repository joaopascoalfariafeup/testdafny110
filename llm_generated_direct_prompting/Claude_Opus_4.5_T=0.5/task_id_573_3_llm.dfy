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
    calc {
        SetProduct(s');
        == { assert s' != {}; }
        var y :| y in s'; y * SetProduct(s' - {y});
    }
    if s == {} {
        assert s' == {x};
        assert SetProduct(s') == x * SetProduct({} );
        assert SetProduct({}) == 1;
        assert SetProduct(s') == x;
        assert SetProduct(s) == 1;
        assert SetProduct(s') == SetProduct(s) * x;
    } else {
        SetProductAddHelper(s, x);
    }
}

lemma SetProductAddHelper(s: set<int>, x: int)
    requires x !in s
    requires s != {}
    ensures SetProduct(s + {x}) == SetProduct(s) * x
{
    var s' := s + {x};
    var y :| y in s';
    if y == x {
        assert s' - {x} == s;
        assert SetProduct(s') == x * SetProduct(s);
    } else {
        assert y in s;
        var s1 := s - {y};
        assert s' - {y} == s1 + {x};
        assert x !in s1;
        SetProductAddHelper2(s, s', x, y);
    }
}

lemma SetProductAddHelper2(s: set<int>, s': set<int>, x: int, y: int)
    requires x !in s
    requires s != {}
    requires s' == s + {x}
    requires y in s
    requires y != x
    ensures SetProduct(s') == SetProduct(s) * x
    decreases |s|
{
    if |s| == 1 {
        assert s == {y};
        assert s' == {y, x};
        assert SetProduct({y}) == y * SetProduct({});
        assert SetProduct({y}) == y;
        
        assert x in s';
        assert s' - {x} == {y};
        
        assert y in s';
        assert s' - {y} == {x};
        assert SetProduct({x}) == x;
        
        SetProductCommute2(x, y);
        assert SetProduct(s') == x * y;
        assert SetProduct(s') == SetProduct(s) * x;
    } else {
        var z :| z in s && z != y;
        var s1 := s - {z};
        assert z !in s1;
        assert |s1| < |s|;
        assert s == s1 + {z};
        
        var s1' := s1 + {x};
        assert x !in s1;
        
        SetProductAddHelper2(s1, s1', x, y);
        assert SetProduct(s1') == SetProduct(s1) * x;
        
        assert z !in s1';
        SetProductAdd(s1', z);
        assert SetProduct(s1' + {z}) == SetProduct(s1') * z;
        assert s1' + {z} == s';
        
        SetProductAdd(s1, z);
        assert SetProduct(s1 + {z}) == SetProduct(s1) * z;
        assert s1 + {z} == s;
        
        calc {
            SetProduct(s');
            == SetProduct(s1') * z;
            == (SetProduct(s1) * x) * z;
            == SetProduct(s1) * x * z;
            == SetProduct(s1) * z * x;
            == (SetProduct(s1) * z) * x;
            == SetProduct(s) * x;
        }
    }
}

lemma SetProductCommute2(x: int, y: int)
    ensures SetProduct({x, y}) == x * y
{
    var s := {x, y};
    if x == y {
        assert s == {x};
        assert SetProduct({x}) == x * SetProduct({});
        assert SetProduct({x}) == x;
        assert x * y == x * x;
    } else {
        assert x in s;
        assert s - {x} == {y};
        assert SetProduct({y}) == y;
    }
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




// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 3 && a1[3] == 2 && a1[4] == 3;
  ghost var s1: set<int> := {1, 2, 3};
  assert forall k :: 0 <= k < a1.Length ==> a1[k] in s1;
  assert forall x :: x in s1 ==> exists k :: 0 <= k < a1.Length && a1[k] == x;
  assert SetProduct({}) == 1;
  SetProductAdd({}, 1);
  assert SetProduct({1}) == 1;
  SetProductAdd({1}, 2);
  assert SetProduct({1, 2}) == 2;
  SetProductAdd({1, 2}, 3);
  assert SetProduct({1, 2, 3}) == 6;
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  ghost var s2: set<int> := {7, 8, 9, 0, 1};
  assert a2[0] == 7 && a2[1] == 8 && a2[2] == 9 && a2[3] == 0 && a2[4] == 1 && a2[5] == 1;
  assert forall k :: 0 <= k < a2.Length ==> a2[k] in s2;
  assert forall x :: x in s2 ==> exists k :: 0 <= k < a2.Length && a2[k] == x;
  SetProductAdd({}, 7);
  assert SetProduct({7}) == 7;
  SetProductAdd({7}, 8);
  assert SetProduct({7, 8}) == 56;
  SetProductAdd({7, 8}, 9);
  assert SetProduct({7, 8, 9}) == 504;
  SetProductAdd({7, 8, 9}, 0);
  assert SetProduct({7, 8, 9, 0}) == 0;
  SetProductAdd({7, 8, 9, 0}, 1);
  assert SetProduct({7, 8, 9, 0, 1}) == 0;
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
