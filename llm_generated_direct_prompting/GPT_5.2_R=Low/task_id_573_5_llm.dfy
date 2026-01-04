// Difficult example because of the need for auxiliary lemmas.

function ElemSet(s: seq<int>): set<int> {
  set x | exists i :: 0 <= i < |s| && s[i] == x
}

function SetProduct(S: set<int>): int
  decreases |S|
{
  if |S| == 0 then 1
  else
    var x : int :| x in S;
    x * SetProduct(S - {x})
}

lemma LemmaSetMinusComm(S: set<int>, x: int, y: int)
  ensures (S - {x}) - {y} == (S - {y}) - {x}
{
  assert forall z :: z in ((S - {x}) - {y}) <==> z in ((S - {y}) - {x});
}

lemma LemmaSetMinusAddFresh(S: set<int>, x: int)
  requires x !in S
  ensures (S + {x}) - {x} == S
{
  assert forall z :: z in ((S + {x}) - {x}) <==> z in S;
}

lemma LemmaSetProductAnyElement(S: set<int>, z: int)
  requires z in S
  ensures SetProduct(S) == z * SetProduct(S - {z})
  decreases |S|
{
  if |S| == 1 {
    assert S == {z};
  } else {
    var y : int :| y in S;
    if y == z {
    } else {
      assert y in S - {z};
      LemmaSetProductAnyElement(S - {y}, z);
      LemmaSetProductAnyElement(S - {z}, y);
      LemmaSetMinusComm(S, y, z);
      calc {
        SetProduct(S);
        == { }
        y * SetProduct(S - {y});
        == { LemmaSetProductAnyElement(S - {y}, z) }
        y * (z * SetProduct((S - {y}) - {z}));
        == { LemmaSetMinusComm(S, y, z) }
        y * (z * SetProduct((S - {z}) - {y}));
        == { }
        (y * z) * SetProduct((S - {z}) - {y});
        == { assert y * z == z * y; }
        (z * y) * SetProduct((S - {z}) - {y});
        == { }
        z * (y * SetProduct((S - {z}) - {y}));
        == { LemmaSetProductAnyElement(S - {z}, y) }
        z * SetProduct(S - {z});
      }
    }
  }
}

lemma LemmaSetProductAddFresh(S: set<int>, x: int)
  requires x !in S
  ensures SetProduct(S + {x}) == x * SetProduct(S)
{
  LemmaSetProductAnyElement(S + {x}, x);
  LemmaSetMinusAddFresh(S, x);
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == SetProduct(ElemSet(a[..a.Length]))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == ElemSet(a[..i])
      invariant product == SetProduct(seen)
    {
        if a[i] !in seen {
            assert a[i] !in ElemSet(a[..i]);
            seen := seen + {a[i]};
            LemmaSetProductAddFresh(ElemSet(a[..i]), a[i]);
            product := product * a[i];
            assert product == SetProduct(seen);
        }
    }
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
