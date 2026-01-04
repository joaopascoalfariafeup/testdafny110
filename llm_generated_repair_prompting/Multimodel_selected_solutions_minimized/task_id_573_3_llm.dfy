// Difficult example because of the need for auxiliary lemmas.

ghost function SetProduct(s: set<int>): int
{
    if s == {} then 1
    else var x :| x in s; x * SetProduct(s - {x})
}

lemma SetProductAdd(s: set<int>, x: int)
    requires x !in s
    ensures SetProduct(s + {x}) == SetProduct(s) * x
{
    var s' := s + {x};
    SetProductCommutative(s', x);
}

lemma SetProductCommutative(s: set<int>, x: int)
    requires x in s
    ensures SetProduct(s) == x * SetProduct(s - {x})
{
    var y :| y in s && SetProduct(s) == y * SetProduct(s - {y});
    if x == y {
    } else {
        var s1 := s - {y};
        var s2 := s - {x};
        SetProductCommutative(s2, y);
        assert s1 - {x} == s2 - {y};
    }
}

lemma SetProductZero(s: set<int>)
    requires 0 in s
    ensures SetProduct(s) == 0
{
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
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 3 && a1[3] == 2 && a1[4] == 3;
  var s1 := set i | 0 <= i < a1.Length :: a1[i];
  assert s1 == {1, 2, 3};
  SetProductAdd({1, 2}, 3);
  assert {1, 2} + {3} == {1, 2, 3};
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert a2[0] == 7 && a2[1] == 8 && a2[2] == 9 && a2[3] == 0 && a2[4] == 1 && a2[5] == 1;
  var s2 := set i | 0 <= i < a2.Length :: a2[i];
  SetProductZero(s2);
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}