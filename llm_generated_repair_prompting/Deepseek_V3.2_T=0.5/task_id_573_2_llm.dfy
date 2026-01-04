// Difficult example because of the need for auxiliary lemmas.

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  requires a.Length >= 0
  ensures product == ProductOfUnique(a[..])
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant product == ProductOfSet(seen)
      invariant forall x :: x in seen ==> x in a[..i]
      invariant forall x :: x in a[..i] ==> x in seen
    {
        if i < a.Length {
            if a[i] !in seen {
                seen := seen + {a[i]};
                product := product * a[i];
                // Helper assertion to connect ProductOfSet with the update
                assert ProductOfSet(seen) == a[i] * ProductOfSet(seen - {a[i]});
                assert ProductOfSet(seen - {a[i]}) == product / a[i];
            }
        }
    }
}

ghost function ProductOfUnique(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 1 else
    if s[|s|-1] in s[..|s|-1] then
      ProductOfUnique(s[..|s|-1])
    else
      s[|s|-1] * ProductOfUnique(s[..|s|-1])
}

ghost function ProductOfSet(s: set<int>): int
  decreases s
{
  if s == {} then 1 else
    var x :| x in s;
    x * ProductOfSet(s - {x})
}

lemma ProductOfSetLemma(s: set<int>, x: int)
  requires x !in s
  ensures ProductOfSet(s + {x}) == x * ProductOfSet(s)
{
  // Proof by calculation
  calc {
    ProductOfSet(s + {x});
    == { 
      // Since x !in s, we can pick x as the element to extract
      var y :| y in s + {x};
      y * ProductOfSet((s + {x}) - {y});
    }
    x * ProductOfSet((s + {x}) - {x});
    == { assert (s + {x}) - {x} == s; }
    x * ProductOfSet(s);
  }
}

lemma ProductOfUniqueLemma(s: seq<int>)
  ensures ProductOfUnique(s) == ProductOfSet(set x | x in s)
  decreases |s|
{
  if |s| == 0 {
    // Base case: empty sequence
    assert ProductOfUnique(s) == 1;
    assert ProductOfSet(set x | x in s) == ProductOfSet({}) == 1;
  } else {
    // Inductive case
    var last := s[|s|-1];
    var prefix := s[..|s|-1];
    ProductOfUniqueLemma(prefix);  // Recursive call for prefix
    
    if last in prefix {
      // last is a duplicate
      calc {
        ProductOfUnique(s);
        == // by definition
        ProductOfUnique(prefix);
        == // by induction hypothesis
        ProductOfSet(set x | x in prefix);
        == { assert set x | x in s == set x | x in prefix; }
        ProductOfSet(set x | x in s);
      }
    } else {
      // last is unique in s
      calc {
        ProductOfUnique(s);
        == // by definition
        last * ProductOfUnique(prefix);
        == // by induction hypothesis
        last * ProductOfSet(set x | x in prefix);
        == { 
          assert set x | x in s == (set x | x in prefix) + {last};
          assert last !in set x | x in prefix;
          ProductOfSetLemma(set x | x in prefix, last);
        }
        ProductOfSet(set x | x in s);
      }
    }
  }
}

// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  // Helper assertions about the array
  assert a1[..] == [1, 2, 3, 2, 3];
  assert set x | x in a1[..] == {1, 2, 3};
  
  var out1 := UniqueProduct(a1);
  // Use the lemma to connect UniqueProduct's postcondition with the set product
  ProductOfUniqueLemma(a1[..]);
  assert ProductOfUnique(a1[..]) == ProductOfSet({1, 2, 3});
  assert ProductOfSet({1, 2, 3}) == 1 * 2 * 3;
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  // Helper assertions about the second array
  assert a2[..] == [7, 8, 9, 0, 1, 1];
  assert set x | x in a2[..] == {7, 8, 9, 0, 1};
  
  var out2 := UniqueProduct(a2);
  // Use the lemma again
  ProductOfUniqueLemma(a2[..]);
  assert ProductOfUnique(a2[..]) == ProductOfSet({7, 8, 9, 0, 1});
  // Since 0 is in the set, the product is 0
  assert 0 in {7, 8, 9, 0, 1};
  assert ProductOfSet({7, 8, 9, 0, 1}) == 0 * ProductOfSet({7, 8, 9, 1});
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}

