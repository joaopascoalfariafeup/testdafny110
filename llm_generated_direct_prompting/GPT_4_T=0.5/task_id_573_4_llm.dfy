// Difficult example because of the need for auxiliary lemmas.

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == Product(UniqueElements(a))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == UniqueElements(a[..i])
      invariant product == Product(UniqueElements(a[..i]))
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
    }
}

// Auxiliary function to calculate the product of a sequence of integers
function Product(s: seq<int>): int
{
   if |s| == 0 then 1 else s[0] * Product(s[1..])
}

// Auxiliary function to extract unique elements from a sequence
function UniqueElements(s: seq<int>): set<int>
{
  if |s| == 0 then {} else if s[0] in UniqueElements(s[1..]) then UniqueElements(s[1..]) else {s[0]} + UniqueElements(s[1..])
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
