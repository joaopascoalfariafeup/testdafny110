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
      invariant forall x :: x in seen ==> exists k :: 0 <= k < i && a[k] == x
      invariant forall k :: 0 <= k < i ==> a[k] in seen
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
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

lemma {:axiom} ProductOfUniqueLemma(s: seq<int>, seen: set<int>)
  requires forall x :: x in seen ==> exists k :: 0 <= k < |s| && s[k] == x
  requires forall k :: 0 <= k < |s| ==> s[k] in seen
  ensures ProductOfUnique(s) == ProductOfSet(seen)
{
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
