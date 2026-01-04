// Difficult example because of the need for auxiliary lemmas.

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
   ensures product == SetProduct(elems(a))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
        invariant seen == elems(a, i)
        invariant product == SetProduct(seen)
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
            SetProductLemma(seen, a[i]); // helper
        }
    }
}

// Auxiliary function that gets the set of distinct elements in array 
// 'a' up to a given length.
ghost function elems<T>(a: array<T>, len: nat := a.Length) : set<T> 
    reads a
    requires len <= a.Length
{
    set x | x in a[..len]
}

// Auxiliary function that returns the product of elements in a set.
ghost function SetProduct(s : set<int>) : int  {
    if s == {} then 1
    else var x :| x in s;
         x * SetProduct(s - {x})
}

// Lemma that proves by induction that the result of SetProduct is the same  
// irrespective of the first element selected non deterministically in SetProduct.
lemma SetProductLemma(s: set<int>, y: int)
   requires y in s
   ensures SetProduct(s) == y * SetProduct(s - {y}) 
{
    var x :| x in s && SetProduct(s) == x * SetProduct(s-{x}); // must exist by def and y in s
    if x != y { 
        calc == {
            SetProduct(s);
            //x * SetProduct(s - {x}); (filled in by Dafny)
            { SetProductLemma(s - {x}, y); }
            //x * (y * SetProduct(s - {x} - {y}));
            {assert s - {x} - {y} == s - {y} - {x};}
            //y * (x * SetProduct(s - {y} - {x}));
            {SetProductLemma(s - {y}, x);}
            y * SetProduct(s - {y});
        }
    }
}

// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert elems(a1) == {a1[0], a1[1], a1[2]}; // helper
  SetProductLemma({1, 2, 3}, 3); // helper: 1 can be the first in the product
  assert {1, 2, 3} - {3} == {1, 2}; // helper
  SetProductLemma({1, 2}, 2); // helper: 2 can be the second in the product
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert a2[3] == 0; // helper
  SetProductLemma(elems(a2), 0); // helper: 0 can be the first in the product
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}