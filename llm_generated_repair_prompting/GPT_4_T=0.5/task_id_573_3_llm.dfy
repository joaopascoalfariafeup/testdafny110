
// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  requires a != null
  ensures product == ProductOfUniqueElements(a[..]) // Pass 'a' as a sequence
{
    product := 1;
    var seen : set<int> := {};

    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == ToSet(a[..i])
      invariant product == ProductOfUniqueElements(a[..i])
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
    }
}

// Auxiliary function to calculate the product of unique elements in a sequence.
function ProductOfUniqueElements(s: seq<int>): int
{
    if |s| == 0 then 1 else if s[|s|-1] in s[..|s|-1] then ProductOfUniqueElements(s[..|s|-1]) else s[|s|-1] * ProductOfUniqueElements(s[..|s|-1])
}

// Ghost function to convert a subarray to a set.
ghost function ToSet(a: seq<int>): set<int> 
{
    if |a| == 0 then {} else {a[|a|-1]} + ToSet(a[..|a|-1])
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

