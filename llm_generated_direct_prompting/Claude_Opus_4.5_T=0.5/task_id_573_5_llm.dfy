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
        assert SetProduct({}) == 1;
        assert SetProduct({y}) == y;
        
        assert SetProduct(s') == SetProduct({y, x});
        var z :| z in s'; 
        if z == x {
            assert s' - {x} == {y};
            assert SetProduct(s') == x * SetProduct({y}) == x * y;
        } else {
            assert z == y;
            assert s' - {y} == {x};
            assert SetProduct({x}) == x * SetProduct({}) == x;
            assert SetProduct(s') == y * SetProduct({x}) == y * x;
        }
        assert SetProduct(s') == x * y;
        assert SetProduct(s) == y;
        assert SetProduct(s') == SetProduct(s) * x;
    } else {
        var s1 := s - {y};
        assert |s1| < |s|;
        assert x !in s1;
        assert s1 != {} || |s| == 1;
        if s1 == {} {
            assert |s| == 1;
        } else {
            SetProductAddHelper(s1, x);
            assert SetProduct(s1 + {x}) == SetProduct(s1) * x;
            
            assert s == s1 + {y};
            assert y !in s1;
            SetProductAddHelper(s1, y);
            assert SetProduct(s) == SetProduct(s1) * y;
            
            assert s' == s1 + {x} + {y};
            assert s1 + {x} + {y} == s1 + {y} + {x};
            var s1x := s1 + {x};
            assert y !in s1x;
            SetProductAddHelper(s1x, y);
            assert SetProduct(s1x + {y}) == SetProduct(s1x) * y;
            assert SetProduct(s1x) == SetProduct(s1) * x;
            assert SetProduct(s') == SetProduct(s1) * x * y;
            assert SetProduct(s) == SetProduct(s1) * y;
            assert SetProduct(s') == SetProduct(s) * x;
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
  var s1 := set i | 0 <= i < a1.Length :: a1[i];
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 3 && a1[3] == 2 && a1[4] == 3;
  assert s1 == {1, 2, 3};
  assert SetProduct({1}) == 1 * SetProduct({}) == 1;
  assert 2 !in {1};
  SetProductAdd({1}, 2);
  assert SetProduct({1, 2}) == 2;
  assert 3 !in {1, 2};
  SetProductAdd({1, 2}, 3);
  assert SetProduct({1, 2, 3}) == 6;
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  var s2 := set i | 0 <= i < a2.Length :: a2[i];
  assert a2[0] == 7 && a2[1] == 8 && a2[2] == 9 && a2[3] == 0 && a2[4] == 1 && a2[5] == 1;
  assert s2 == {7, 8, 9, 0, 1};
  assert 0 in s2;
  ZeroInSetProduct(s2, 0);
  assert SetProduct(s2) == 0;
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}

lemma ZeroInSetProduct(s: set<int>, z: int)
    requires z in s
    requires z == 0
    ensures SetProduct(s) == 0
    decreases |s|
{
    if |s| == 1 {
        assert s == {0};
        assert SetProduct(s) == 0 * SetProduct({}) == 0;
    } else {
        var x :| x in s;
        var s' := s - {x};
        if x == 0 {
            assert SetProduct(s) == 0 * SetProduct(s') == 0;
        } else {
            assert z in s';
            ZeroInSetProduct(s', z);
            assert SetProduct(s') == 0;
            assert SetProduct(s) == x * SetProduct(s') == x * 0 == 0;
        }
    }
}
