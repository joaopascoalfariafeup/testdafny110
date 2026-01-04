
// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  requires a != null
  ensures product == ProductOfUniqueElements(ToSet(a[..])) // Pass 'a' as a sequence
{
    product := 1;
    var seen : set<int> := {};

    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == ToSet(a[..i])
      invariant product == ProductOfUniqueElements(seen)
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
    }
}

// Auxiliary function to calculate the product of unique elements in a sequence.
ghost function ProductOfUniqueElements(s: set<int>): int
  decreases |s|
{
    if |s| == 0 then 1 else Arbitrary(s) * ProductOfUniqueElements(s - {Arbitrary(s)})
}

// Ghost function to convert a subarray to a set.
ghost function ToSet(a: seq<int>): set<int> 
  decreases |a|
{
    if |a| == 0 then {} else {a[0]} + ToSet(a[1..])
}

// Ghost function to get an arbitrary element from a set.
ghost function Arbitrary(s: set<int>): int
  requires s != {}
{
  var i := some x | x in s;
  i
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

