// Difficult example because of the need for auxiliary lemmas.

function Prod(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 1 else Prod(s[..|s|-1]) * s[|s|-1]
}

function UniqueSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else
    var u := UniqueSeq(s[..|s|-1]);
    if s[|s|-1] in set u then u else u + [s[|s|-1]]
}

lemma UniqueSeqChar(s: seq<int>)
  ensures set UniqueSeq(s) == set s
  ensures forall x :: x in set UniqueSeq(s) ==> x in set s
  ensures forall x :: x in set s ==> x in set UniqueSeq(s)
{
}

lemma UniqueSeqStep(s: seq<int>)
  requires |s| > 0
  ensures UniqueSeq(s) ==
    (if s[|s|-1] in set UniqueSeq(s[..|s|-1]) then UniqueSeq(s[..|s|-1]) else UniqueSeq(s[..|s|-1]) + [s[|s|-1]])
{
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == Prod(UniqueSeq(a[..]))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == set UniqueSeq(a[..i])
      invariant product == Prod(UniqueSeq(a[..i]))
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
        assert i + 1 <= a.Length;
        assert seen == set UniqueSeq(a[..i+1]);
        assert product == Prod(UniqueSeq(a[..i+1]));
    }
    assert product == Prod(UniqueSeq(a[..a.Length]));
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
