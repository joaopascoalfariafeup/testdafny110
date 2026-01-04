// Difficult example because of the need for auxiliary lemmas.

function {:fuel 50} UniqueProd(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then
    1
  else if s[|s|-1] in set s[..|s|-1] then
    UniqueProd(s[..|s|-1])
  else
    UniqueProd(s[..|s|-1]) * s[|s|-1]
}

lemma UniqueProdExtend(s: seq<int>, x: int)
  ensures UniqueProd(s + [x]) == (if x in set s then UniqueProd(s) else UniqueProd(s) * x)
{
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == UniqueProd(a[..])
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == set a[..i]
      invariant product == UniqueProd(a[..i])
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
        assert UniqueProd(a[..i+1]) == (if a[i] in set a[..i] then UniqueProd(a[..i]) else UniqueProd(a[..i]) * a[i]);
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
