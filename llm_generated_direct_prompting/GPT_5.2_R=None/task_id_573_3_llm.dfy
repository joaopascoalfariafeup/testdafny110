// Difficult example because of the need for auxiliary lemmas.

ghost function Prod(s: seq<int>): int
{
  if |s| == 0 then 1 else Prod(s[..|s|-1]) * s[|s|-1]
}

ghost function UniqueSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else
    var t := UniqueSeq(s[..|s|-1]);
    if s[|s|-1] in set t then t else t + [s[|s|-1]]
}

lemma ProdAppend(s: seq<int>, x: int)
  ensures Prod(s + [x]) == Prod(s) * x
{
}

lemma UniqueSeqPrefixProperty(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures set UniqueSeq(s[..i]) == set s[..i]
  decreases i
{
  if i == 0 {
  } else {
    UniqueSeqPrefixProperty(s, i-1);
  }
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == Prod(UniqueSeq(a[..]))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == set a[..i]
      invariant product == Prod(UniqueSeq(a[..i]))
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];

            assert set UniqueSeq(a[..i] + [a[i]]) == set UniqueSeq(a[..i]) + {a[i]};
            assert a[i] !in set UniqueSeq(a[..i]);
            ProdAppend(UniqueSeq(a[..i]), a[i]);
        } else {
            assert a[i] in set a[..i];
            UniqueSeqPrefixProperty(a[..], i);
            assert a[i] in set UniqueSeq(a[..i]);
            assert UniqueSeq(a[..i] + [a[i]]) == UniqueSeq(a[..i]);
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
