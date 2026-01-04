// Difficult example because of the need for auxiliary lemmas.

ghost function SetProduct(s: set<int>): int
{
    if s == {} then 1
    else var x :| x in s; x * SetProduct(s - {x})
}

ghost function SeqToSet(s: seq<int>): set<int>
{
    if |s| == 0 then {}
    else {s[|s|-1]} + SeqToSet(s[..|s|-1])
}

lemma SetProductZero(s: set<int>)
    requires 0 in s
    ensures SetProduct(s) == 0
{
    if s == {} {
    } else {
        var x :| x in s;
        if x == 0 {
            assert s - {x} == s - {0};
            SetProductZero_helper(s, 0);
        } else {
            assert 0 in s - {x};
            SetProductZero(s - {x});
        }
    }
}

lemma SetProductZero_helper(s: set<int>, x: int)
    requires x in s
    requires x == 0
    ensures SetProduct(s) == 0
{
    if s == {} {
    } else {
        var y :| y in s;
        if y == 0 {
            // SetProduct(s) == 0 * SetProduct(s - {0})
        } else {
            assert 0 in s - {y};
            SetProductZero(s - {y});
        }
    }
}

lemma SetProductInsert(s: set<int>, x: int)
    requires x !in s
    ensures SetProduct(s + {x}) == x * SetProduct(s)
{
    var s' := s + {x};
    assert x in s';
    if s' == {} {
    } else {
        var y :| y in s';
        if y == x {
            assert s' - {y} == s;
        } else {
            assert y in s;
            calc {
                SetProduct(s');
                == y * SetProduct(s' - {y});
                == { assert s' - {y} == s - {y} + {x}; 
                     SetProductInsert(s - {y}, x); }
                y * (x * SetProduct(s - {y}));
                == x * (y * SetProduct(s - {y}));
                == { assert y in s; }
                x * SetProduct(s);
            }
        }
    }
}

lemma SetProductSingleton(x: int)
    ensures SetProduct({x}) == x
{
    assert {x} - {x} == {};
    assert SetProduct({}) == 1;
}

lemma SetProduct123()
    ensures SetProduct({1, 2, 3}) == 6
{
    SetProductInsert({}, 1);
    assert SetProduct({1}) == 1;
    SetProductInsert({1}, 2);
    assert SetProduct({1, 2}) == 2;
    SetProductInsert({1, 2}, 3);
    assert SetProduct({1, 2, 3}) == 6;
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
    ensures product == SetProduct(SeqToSet(a[..]))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
        invariant seen == SeqToSet(a[..i])
        invariant product == SetProduct(seen)
    {
        if a[i] !in seen {
            SetProductInsert(seen, a[i]);
            seen := seen + {a[i]};
            product := product * a[i];
        }
        assert seen == SeqToSet(a[..i+1]) by {
            assert a[..i+1] == a[..i] + [a[i]];
            assert SeqToSet(a[..i+1]) == {a[i]} + SeqToSet(a[..i]);
        }
    }
    assert a[..a.Length] == a[..];
}




// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert a1[..] == [1, 2, 3, 2, 3];
  assert SeqToSet([1, 2, 3, 2, 3]) == {1, 2, 3};
  SetProduct123();
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert a2[..] == [7, 8, 9, 0, 1, 1];
  assert SeqToSet([7, 8, 9, 0, 1, 1]) == {7, 8, 9, 0, 1};
  assert 0 in {7, 8, 9, 0, 1};
  SetProductZero({7, 8, 9, 0, 1});
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
