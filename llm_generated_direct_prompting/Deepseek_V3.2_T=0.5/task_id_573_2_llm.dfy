// Difficult example because of the need for auxiliary lemmas.

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  requires a.Length >= 0
  ensures product == ProductOfSet(ToSet(a[..]))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant product == ProductOfSet(seen)
      invariant seen <= ToSet(a[..])
      invariant forall x :: x in seen ==> x in a[..i]
      invariant forall x :: x in a[..i] ==> x in seen
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
    }
}

ghost function ToSet(s: seq<int>): set<int>
  ensures |s| == 0 ==> ToSet(s) == {}
  ensures |s| > 0 ==> ToSet(s) == {s[|s|-1]} + ToSet(s[..|s|-1])
{
  if |s| == 0 then {} else {s[|s|-1]} + ToSet(s[..|s|-1])
}

ghost function ProductOfSet(s: set<int>): int
  decreases s
  ensures s == {} ==> ProductOfSet(s) == 1
  ensures forall x :: x in s ==> ProductOfSet(s) == x * ProductOfSet(s - {x})
{
  if s == {} then 1 else
    var x :| x in s;
    x * ProductOfSet(s - {x})
}

lemma ProductOfSetUnion(s1: set<int>, s2: set<int>)
  requires s1 !! s2
  ensures ProductOfSet(s1 + s2) == ProductOfSet(s1) * ProductOfSet(s2)
{
}

lemma ProductOfSetContains(s: set<int>, x: int)
  requires x in s
  ensures ProductOfSet(s) == x * ProductOfSet(s - {x})
{
}

lemma ToSetSlice(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures ToSet(s[..i]) <= ToSet(s)
{
}

lemma ToSetAppend(s1: seq<int>, s2: seq<int>)
  ensures ToSet(s1 + s2) == ToSet(s1) + ToSet(s2)
{
}

lemma ToSetContains(s: seq<int>, x: int)
  ensures x in ToSet(s) <==> x in s
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
