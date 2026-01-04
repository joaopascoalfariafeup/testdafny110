// Difficult example because of the need for auxiliary lemmas.

function SeqSet(s: seq<int>): set<int> {
  set x | exists i :: 0 <= i < |s| && s[i] == x
}

function {:fuel 0} UniqueSeq(s: seq<int>): seq<int> {
  if |s| == 0 then
    []
  else
    var t := UniqueSeq(s[..|s|-1]);
    if s[|s|-1] in SeqSet(t) then t else t + [s[|s|-1]]
}

function {:fuel 0} Prod(s: seq<int>): int {
  if |s| == 0 then 1 else Prod(s[..|s|-1]) * s[|s|-1]
}

lemma SeqSetAppend(s: seq<int>, x: int)
  ensures SeqSet(s + [x]) == SeqSet(s) + {x}
{
  assert SeqSet(s + [x]) <= SeqSet(s) + {x};
  assert SeqSet(s) + {x} <= SeqSet(s + [x]);
}

lemma SeqSetUniqueSeq(s: seq<int>)
  ensures SeqSet(UniqueSeq(s)) == SeqSet(s)
{
  if |s| == 0 {
  } else {
    SeqSetUniqueSeq(s[..|s|-1]);
    var t := UniqueSeq(s[..|s|-1]);
    var x := s[|s|-1];
    if x in SeqSet(t) {
      assert UniqueSeq(s) == t;
    } else {
      assert UniqueSeq(s) == t + [x];
      SeqSetAppend(t, x);
    }
    assert SeqSet(UniqueSeq(s)) == SeqSet(s);
  }
}

lemma UniqueSeqAppend(s: seq<int>, x: int)
  ensures UniqueSeq(s + [x]) == (if x in SeqSet(s) then UniqueSeq(s) else UniqueSeq(s) + [x])
{
  SeqSetUniqueSeq(s);
  var t := UniqueSeq(s);
  if x in SeqSet(s) {
    assert x in SeqSet(t);
    assert UniqueSeq(s + [x]) == t;
  } else {
    assert x !in SeqSet(t);
    assert UniqueSeq(s + [x]) == t + [x];
  }
}

lemma ProdAppend(s: seq<int>, x: int)
  ensures Prod(s + [x]) == Prod(s) * x
{
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == Prod(UniqueSeq(a[..]))
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant seen == SeqSet(a[..i])
      invariant product == Prod(UniqueSeq(a[..i]))
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
        SeqSetAppend(a[..i], a[i]);
        UniqueSeqAppend(a[..i], a[i]);
        ProdAppend(UniqueSeq(a[..i]), a[i]);
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
