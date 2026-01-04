// Difficult example because of the need for auxiliary lemmas.

function {:fuel 10} ProductSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 1 else ProductSeq(s[..|s|-1]) * s[|s|-1]
}

function {:fuel 10} UniqueSeq(a: array<int>, n: int): seq<int>
  requires a != null
  requires 0 <= n <= a.Length
  reads a
  decreases n
{
  if n == 0 then []
  else
    (let prev := UniqueSeq(a, n-1) in
      if a[n-1] in set prev then prev else prev + [a[n-1]])
}

lemma SetOfAppend(s: seq<int>, x: int)
  ensures set(s + [x]) == set(s) + {x}
{
  // mutual subset
  forall y | y in set(s + [x])
    ensures y in set(s) + {x}
  {
    if y == x {
    } else {
      // from y in set(s+[x]), pick an index witnessing membership
      var k :| 0 <= k < |s + [x]| && (s + [x])[k] == y;
      assert |s + [x]| == |s| + 1;
      if k == |s| {
        assert (s + [x])[|s|] == x;
        assert false;
      } else {
        assert 0 <= k < |s|;
        assert (s + [x])[k] == s[k];
        assert s[k] == y;
        assert y in set(s);
      }
    }
  }

  forall y | y in set(s) + {x}
    ensures y in set(s + [x])
  {
    if y == x {
      assert |s + [x]| == |s| + 1;
      assert 0 <= |s| < |s + [x]|;
      assert (s + [x])[|s|] == x;
    } else {
      assert y in set(s);
      var k :| 0 <= k < |s| && s[k] == y;
      assert |s + [x]| == |s| + 1;
      assert 0 <= k < |s + [x]|;
      assert (s + [x])[k] == s[k];
      assert (s + [x])[k] == y;
    }
  }
}

lemma ProdAppend(s: seq<int>, x: int)
  ensures ProductSeq(s + [x]) == ProductSeq(s) * x
{
  assert |s + [x]| == |s| + 1;
  assert |s + [x]| > 0;
  assert (s + [x])[|s + [x]| - 1] == x;
  assert (s + [x])[..|s + [x]| - 1] == s;

  calc {
    ProductSeq(s + [x]);
    == { }
    ProductSeq((s + [x])[..|s + [x]| - 1]) * (s + [x])[|s + [x]| - 1];
    == { }
    ProductSeq(s) * x;
  }
}

lemma UniqueSeqStep(a: array<int>, i: int)
  requires a != null
  requires 0 <= i < a.Length
  reads a
  ensures UniqueSeq(a, i+1) ==
            (if a[i] in set UniqueSeq(a, i) then UniqueSeq(a, i) else UniqueSeq(a, i) + [a[i]])
{
  // Unfold UniqueSeq at n = i+1
  calc {
    UniqueSeq(a, i+1);
    == { }
    (let prev := UniqueSeq(a, i) in
     if a[i] in set prev then prev else prev + [a[i]]);
    == { }
    (if a[i] in set UniqueSeq(a, i) then UniqueSeq(a, i) else UniqueSeq(a, i) + [a[i]]);
  }
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  requires a != null
  ensures product == ProductSeq(UniqueSeq(a, a.Length))
{
    product := 1;
    var seen : set<int> := {};

    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == set UniqueSeq(a, i)
      invariant product == ProductSeq(UniqueSeq(a, i))
    {
        UniqueSeqStep(a, i);

        if a[i] !in seen {
            assert a[i] !in set UniqueSeq(a, i);

            assert UniqueSeq(a, i+1) ==
              (if a[i] in set UniqueSeq(a, i) then UniqueSeq(a, i) else UniqueSeq(a, i) + [a[i]]);
            assert UniqueSeq(a, i+1) == UniqueSeq(a, i) + [a[i]];

            SetOfAppend(UniqueSeq(a, i), a[i]);
            ProdAppend(UniqueSeq(a, i), a[i]);

            // help the verifier connect updates to the invariants
            assert seen + {a[i]} == set UniqueSeq(a, i) + {a[i]};
            assert product * a[i] == ProductSeq(UniqueSeq(a, i)) * a[i];

            seen := seen + {a[i]};
            product := product * a[i];

            // Re-establish invariants for i+1
            assert set UniqueSeq(a, i+1) == set (UniqueSeq(a, i) + [a[i]]);
            assert seen == set UniqueSeq(a, i+1);
            assert product == ProductSeq(UniqueSeq(a, i+1));
        } else {
            assert a[i] in set UniqueSeq(a, i);

            assert UniqueSeq(a, i+1) ==
              (if a[i] in set UniqueSeq(a, i) then UniqueSeq(a, i) else UniqueSeq(a, i) + [a[i]]);
            assert UniqueSeq(a, i+1) == UniqueSeq(a, i);

            // Re-establish invariants for i+1 (no state change)
            assert seen == set UniqueSeq(a, i+1);
            assert product == ProductSeq(UniqueSeq(a, i+1));
        }
    }
}




// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  assert a1[..] == [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  assert a2[..] == [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
