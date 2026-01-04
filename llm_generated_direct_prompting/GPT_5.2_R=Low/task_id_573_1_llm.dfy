// Difficult example because of the need for auxiliary lemmas.

function Prod(s: seq<int>): int
{
  if |s| == 0 then 1 else Prod(s[..|s|-1]) * s[|s|-1]
}

function UniqueSeqPrefix(s: seq<int>, n: nat): seq<int>
  requires n <= |s|
  decreases n
{
  if n == 0 then []
  else
    var t := UniqueSeqPrefix(s, n-1);
    if s[n-1] in set t then t else t + [s[n-1]]
}

function UniqueSeq(s: seq<int>): seq<int>
{
  UniqueSeqPrefix(s, |s|)
}

lemma SetOfAppend<T>(t: seq<T>, x: T)
  ensures set (t + [x]) == set t + {x}
{
  assert forall y: T :: (y in set (t + [x])) <==> (y in set t + {x}) by
  {
    intro y;
    if y == x {
      assert y in set (t + [x]);
      assert y in set t + {x};
    } else {
      assert (y in set (t + [x])) <==> (y in set t);
      assert (y in set t) <==> (y in set t + {x});
    }
  }
}

lemma ProdAppend(t: seq<int>, x: int)
  ensures Prod(t + [x]) == Prod(t) * x
{
  assert |t + [x]| == |t| + 1;
  assert (t + [x])[|t + [x]| - 1] == x;
  assert (t + [x])[..|t + [x]| - 1] == t;
}

lemma UniqueSeqPrefixStep(s: seq<int>, n: nat)
  requires n < |s|
  ensures UniqueSeqPrefix(s, n+1) ==
            (if s[n] in set UniqueSeqPrefix(s, n)
             then UniqueSeqPrefix(s, n)
             else UniqueSeqPrefix(s, n) + [s[n]])
{
  assert n + 1 <= |s|;
  if n + 1 == 0 {
  } else {
    // Unfold UniqueSeqPrefix(s, n+1)
    assert UniqueSeqPrefix(s, n+1) ==
            (var t := UniqueSeqPrefix(s, (n+1)-1);
             if s[(n+1)-1] in set t then t else t + [s[(n+1)-1]]);
    assert (n+1)-1 == n;
    assert s[(n+1)-1] == s[n];
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
      invariant seen == set UniqueSeqPrefix(a[..], i)
      invariant product == Prod(UniqueSeqPrefix(a[..], i))
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
        }
        assert UniqueSeqPrefix(a[..], i+1) ==
                 (if a[i] in set UniqueSeqPrefix(a[..], i)
                  then UniqueSeqPrefix(a[..], i)
                  else UniqueSeqPrefix(a[..], i) + [a[i]]) by
        {
          UniqueSeqPrefixStep(a[..], i);
        }

        if a[i] !in seen {
          assert a[i] !in set UniqueSeqPrefix(a[..], i);
          SetOfAppend(UniqueSeqPrefix(a[..], i), a[i]);
          ProdAppend(UniqueSeqPrefix(a[..], i), a[i]);
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
