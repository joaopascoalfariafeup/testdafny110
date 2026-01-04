// Difficult example because of the need for auxiliary lemmas.

ghost function {:fuel 0} SetProduct(s: set<int>): int
{
  if |s| == 0 then 1
  else
    var x :| x in s;
    x * SetProduct(s - {x})
}

lemma SetProductAdd(s: set<int>, x: int)
  requires x !in s
  ensures SetProduct(s + {x}) == SetProduct(s) * x
{
  calc {
    SetProduct(s + {x});
    ==
    x * SetProduct((s + {x}) - {x});
    ==
    x * SetProduct(s);
    ==
    SetProduct(s) * x;
  }
}

method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == SetProduct(set i | 0 <= i < a.Length :: a[i])
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == set j | 0 <= j < i :: a[j]
      invariant product == SetProduct(seen)
    {
        if a[i] !in seen {
            assert a[i] !in seen;
            assert seen == set j | 0 <= j < i :: a[j];
            seen := seen + {a[i]};
            product := product * a[i];
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
  var out1 := UniqueProduct(a1);
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
