// Difficult example because of the need for auxiliary lemmas.

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
    {
        if a[i] !in seen {
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
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}