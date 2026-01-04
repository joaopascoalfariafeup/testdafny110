// Difficult example because of the need for auxiliary lemmas.

// Ghost function to compute the product of a set of integers
function Product(s: set<int>): int
{
  if s == {} then 1 else (var someElement := set#Some(s); someElement * Product(s - {someElement}))
}

// Ghost function to compute the set of unique elements in an array
function UniqueElements(a: array<int>, n: nat): set<int>
{
  if n == 0 then {} else UniqueElements(a, n-1) + {a[n-1]}
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  requires a.Length > 0
  ensures product == Product(UniqueElements(a, a.Length))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant i <= a.Length
      invariant seen == UniqueElements(a, i)
      invariant product == Product(seen)
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
