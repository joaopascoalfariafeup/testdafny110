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
      invariant seen == SetFromSeq(a[..i])
    {
        if i < a.Length {
            if a[i] !in seen {
                seen := seen + {a[i]};
                product := product * a[i];
                // Helper assertion to connect ProductOfSet with the update
                // Use lemma to prove this
                ProductOfSetAdd(seen - {a[i]}, a[i]);
                assert ProductOfSet(seen) == a[i] * ProductOfSet(seen - {a[i]});
                // Don't assert division to avoid division by zero
                // Instead assert the multiplication relationship
                assert ProductOfSet(seen - {a[i]}) == old(product);
            }
        }
    }
    // Final lemma to connect seen with the full sequence
    ProductOfUniqueLemma(a[..]);
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

// Helper function to get set from sequence
ghost function SetFromSeq(s: seq<int>): set<int>
{
  set x | x in s
}

// Lemma connecting ProductOfUnique with ProductOfSet
lemma ProductOfUniqueLemma(s: seq<int>)
  ensures ProductOfUnique(s) == ProductOfSet(SetFromSeq(s))
  decreases |s|
{
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

// Additional lemma to help with product calculations
lemma ProductOfSetZero(s: set<int>)
  requires 0 in s
  ensures ProductOfSet(s) == 0
  decreases s
{
  if s == {} {
    // impossible since 0 in s
  } else {
    var x :| x in s;
    if x == 0 {
      // If we choose 0, then ProductOfSet(s) = 0 * ProductOfSet(s - {0}) = 0
      assert ProductOfSet(s) == 0 * ProductOfSet(s - {0});
      assert ProductOfSet(s) == 0;
    } else {
      // If we choose x != 0, we need to show that eventually 0 will be chosen
      // and the product becomes 0
      ProductOfSetZero(s - {x});
      assert ProductOfSet(s - {x}) == 0;
      assert ProductOfSet(s) == x * ProductOfSet(s - {x});
      assert ProductOfSet(s) == x * 0;
      assert ProductOfSet(s) == 0;
    }
  }
}

// Helper lemma for test assertions
lemma ProductOfSetThree()
  ensures ProductOfSet({1, 2, 3}) == 6
{
  var empty: set<int> := {};
  ProductOfSetAdd(empty, 1);
  assert ProductOfSet({1}) == 1;
  ProductOfSetAdd({1}, 2);
  assert ProductOfSet({1, 2}) == 2;
  ProductOfSetAdd({1, 2}, 3);
  assert ProductOfSet({1, 2, 3}) == 6;
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
  // First, prove the product calculation using lemmas
  // We can compute by repeatedly applying the ProductOfSetAdd lemma
  ProductOfSetThree();
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
  // Use the ProductOfSetZero lemma
  ProductOfSetZero(set2);
  assert ProductOfSet(set2) == 0;
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}

// Additional helper lemma to prove that the set from a sequence prefix is contained in the set from the full sequence
lemma SetFromSeqPrefix(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures SetFromSeq(s[..i]) <= SetFromSeq(s)
{
  // This lemma helps Dafny understand the relationship between sets from prefixes
}

// Helper lemma to prove that if an element is in a set from a sequence, it's in the sequence
lemma InSetFromSeqImpliesInSeq(x: int, s: seq<int>)
  requires x in SetFromSeq(s)
  ensures exists i :: 0 <= i < |s| && s[i] == x
{
  // This lemma helps Dafny understand the relationship between sets and sequences
}

// Helper lemma to prove that if an element is in a sequence prefix, it's in the set from that prefix
lemma InSeqPrefixImpliesInSet(x: int, s: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires x in s[..i]
  ensures x in SetFromSeq(s[..i])
{
  // This lemma helps Dafny understand the relationship between sequences and sets
}

// Helper lemma to prove the main postcondition
lemma UniqueProductPostconditionHelper(a: array<int>, seen: set<int>, i: int)
  requires 0 <= i <= a.Length
  requires forall x :: x in seen ==> x in a[..i]
  requires forall x :: x in a[..i] ==> x in seen
  ensures SetFromSeq(a[..]) == SetFromSeq(a[..i]) + SetFromSeq(a[i..])
  ensures SetFromSeq(a[..]) == seen + SetFromSeq(a[i..])
{
  // This lemma helps Dafny understand how the set evolves through the loop
}

// New lemma to help with the ProductOfSetThree verification
lemma ProductOfSetThreeHelper()
  ensures ProductOfSet({1, 2, 3}) == 6
{
  // Direct computation using the definition
  // Choose 1 from {1, 2, 3}
  assert ProductOfSet({1, 2, 3}) == 1 * ProductOfSet({2, 3});
  // Choose 2 from {2, 3}
  assert ProductOfSet({2, 3}) == 2 * ProductOfSet({3});
  // Choose 3 from {3}
  assert ProductOfSet({3}) == 3 * ProductOfSet({});
  assert ProductOfSet({}) == 1;
  assert ProductOfSet({3}) == 3;
  assert ProductOfSet({2, 3}) == 2 * 3 == 6;
  assert ProductOfSet({1, 2, 3}) == 1 * 6 == 6;
}

// Replace the problematic ProductOfSetThree lemma with the simpler version
lemma ProductOfSetThreeFixed()
  ensures ProductOfSet({1, 2, 3}) == 6
{
  ProductOfSetThreeHelper();
}

