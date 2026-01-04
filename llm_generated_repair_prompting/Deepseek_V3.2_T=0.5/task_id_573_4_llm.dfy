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

// Lemma to show that adding a new element multiplies the product
lemma ProductOfSetAdd(s: set<int>, x: int)
  requires x !in s
  ensures ProductOfSet(s + {x}) == x * ProductOfSet(s)
  decreases |s|
{
  // Proof by induction on the size of s
  if s == {} {
    // Base case
    // Direct calculation
    assert s + {x} == {x};
    var y :| y in {x};
    assert y == x;
    assert ProductOfSet({x}) == x * ProductOfSet({x} - {x});
    assert {x} - {x} == {};
    assert ProductOfSet({}) == 1;
    assert ProductOfSet({x}) == x * 1;
  } else {
    // Inductive case
    var y :| y in s;
    var s' := s - {y};
    // Inductive hypothesis for s'
    ProductOfSetAdd(s', x);
    
    // Now compute ProductOfSet(s + {x})
    // We'll show it equals x * ProductOfSet(s)
    calc {
      ProductOfSet(s + {x});
      == // By definition, choosing y (since y in s, so y in s + {x})
      y * ProductOfSet((s + {x}) - {y});
      == { 
        assert (s + {x}) - {y} == (s - {y}) + {x};
        assert s - {y} == s';
      }
      y * ProductOfSet(s' + {x});
      == { ProductOfSetAdd(s', x); }
      y * (x * ProductOfSet(s'));
      == // Multiplication is commutative
      x * (y * ProductOfSet(s'));
      == { 
        // By definition of ProductOfSet(s) when choosing y
        assert ProductOfSet(s) == y * ProductOfSet(s');
      }
      x * ProductOfSet(s);
    }
  }
}

// Lemma connecting ProductOfUnique with ProductOfSet
lemma ProductOfUniqueLemma(s: seq<int>)
  ensures ProductOfUnique(s) == ProductOfSet(SetFromSeq(s))
  decreases |s|
{
  // Helper function to convert sequence to set
  ghost function SetFromSeq(s: seq<int>): set<int>
  {
    set x | x in s
  }
  
  if |s| == 0 {
    // Base case: empty sequence
    assert ProductOfUnique(s) == 1;
    assert SetFromSeq(s) == {};
    assert ProductOfSet(SetFromSeq(s)) == 1;
  } else {
    // Inductive case
    var last := s[|s|-1];
    var prefix := s[..|s|-1];
    ProductOfUniqueLemma(prefix);  // Recursive call for prefix
    
    // Calculate the set for the prefix
    var prefixSet := SetFromSeq(prefix);
    
    if last in prefix {
      // last is a duplicate
      calc {
        ProductOfUnique(s);
        == // by definition
        ProductOfUnique(prefix);
        == // by induction hypothesis
        ProductOfSet(prefixSet);
        == { 
          // The set of s is the same as the set of prefix since last is already in prefix
          assert SetFromSeq(s) == prefixSet;
        }
        ProductOfSet(SetFromSeq(s));
      }
    } else {
      // last is unique in s
      calc {
        ProductOfUnique(s);
        == // by definition
        last * ProductOfUnique(prefix);
        == // by induction hypothesis
        last * ProductOfSet(prefixSet);
        == { 
          // The set of s is prefixSet plus last
          assert SetFromSeq(s) == prefixSet + {last};
          assert last !in prefixSet;
          ProductOfSetAdd(prefixSet, last);
        }
        ProductOfSet(SetFromSeq(s));
      }
    }
  }
}

// Helper function to get set from sequence
ghost function SetFromSeq(s: seq<int>): set<int>
{
  set x | x in s
}

// Test cases checked statically by Dafny
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  // Helper assertions about the array
  assert a1[..] == [1, 2, 3, 2, 3];
  // Use helper function for set comprehension
  var set1 := SetFromSeq(a1[..]);
  assert set1 == {1, 2, 3};
  
  var out1 := UniqueProduct(a1);
  // Use the lemma to connect UniqueProduct's postcondition with the set product
  ProductOfUniqueLemma(a1[..]);
  assert ProductOfUnique(a1[..]) == ProductOfSet(set1);
  // Calculate ProductOfSet({1, 2, 3}) step by step
  assert ProductOfSet({1, 2, 3}) == 1 * ProductOfSet({2, 3});
  assert ProductOfSet({2, 3}) == 2 * ProductOfSet({3});
  assert ProductOfSet({3}) == 3 * ProductOfSet({});
  assert ProductOfSet({}) == 1;
  assert ProductOfSet({3}) == 3;
  assert ProductOfSet({2, 3}) == 6;
  assert ProductOfSet({1, 2, 3}) == 6;
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  // Helper assertions about the second array
  assert a2[..] == [7, 8, 9, 0, 1, 1];
  var set2 := SetFromSeq(a2[..]);
  assert set2 == {7, 8, 9, 0, 1};
  
  var out2 := UniqueProduct(a2);
  // Use the lemma again
  ProductOfUniqueLemma(a2[..]);
  assert ProductOfUnique(a2[..]) == ProductOfSet(set2);
  // Since 0 is in the set, the product is 0
  assert 0 in set2;
  // Calculate ProductOfSet({7, 8, 9, 0, 1}) step by step
  // When 0 is chosen as the element, the product becomes 0
  assert exists x :: x in set2 && x == 0;
  // We can show that regardless of which element is chosen first, the product is 0
  // because 0 * anything = 0
  assert ProductOfSet(set2) == 0;
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
