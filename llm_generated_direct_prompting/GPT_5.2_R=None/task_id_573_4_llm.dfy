// Difficult example because of the need for auxiliary lemmas.

ghost function {:fuel 0} UniqueProductSeq(s: seq<int>): int
{
  if |s| == 0 then 1
  else if s[|s|-1] in s[..|s|-1] then UniqueProductSeq(s[..|s|-1])
  else UniqueProductSeq(s[..|s|-1]) * s[|s|-1]
}

ghost function SeenSet(s: seq<int>): set<int>
{
  set x | exists k :: 0 <= k < |s| && s[k] == x
}

lemma {:induction n} UniqueProductSeq_ExtendNew(s: seq<int>, x: int, n: nat)
  requires |s| == n
  requires x !in SeenSet(s)
  ensures UniqueProductSeq(s + [x]) == UniqueProductSeq(s) * x
{
}

lemma {:induction n} UniqueProductSeq_ExtendDup(s: seq<int>, x: int, n: nat)
  requires |s| == n
  requires x in SeenSet(s)
  ensures UniqueProductSeq(s + [x]) == UniqueProductSeq(s)
{
}

lemma {:induction n} UniqueProductSeq_Append(s: seq<int>, t: seq<int>, n: nat)
  requires |t| == n
  ensures UniqueProductSeq(s + t) ==
            (if |t| == 0 then UniqueProductSeq(s)
             else if t[|t|-1] in SeenSet(s + t[..|t|-1]) then UniqueProductSeq(s + t[..|t|-1])
             else UniqueProductSeq(s + t[..|t|-1]) * t[|t|-1])
{
}

lemma {:induction n} SeenSet_Extend(s: seq<int>, x: int, n: nat)
  requires |s| == n
  ensures SeenSet(s + [x]) == SeenSet(s) + {x}
{
}

lemma SeenSet_SeqEq(a: array<int>, i: int)
  requires 0 <= i <= a.Length
  ensures SeenSet(a[..i]) == set x | exists k :: 0 <= k < i && a[k] == x
{
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == UniqueProductSeq(a[..])
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == SeenSet(a[..i])
      invariant product == UniqueProductSeq(a[..i])
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
            assert SeenSet(a[..i] + [a[i]]) == SeenSet(a[..i]) + {a[i]};
            assert a[i] !in SeenSet(a[..i]);
            assert UniqueProductSeq(a[..i] + [a[i]]) == UniqueProductSeq(a[..i]) * a[i];
        } else {
            assert a[i] in SeenSet(a[..i]);
            assert UniqueProductSeq(a[..i] + [a[i]]) == UniqueProductSeq(a[..i]);
        }
        assert a[..i+1] == a[..i] + [a[i]];
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
