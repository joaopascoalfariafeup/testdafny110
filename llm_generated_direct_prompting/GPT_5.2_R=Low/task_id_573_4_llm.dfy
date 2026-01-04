// Difficult example because of the need for auxiliary lemmas.

ghost function Seen(s: seq<int>): set<int>
{
  set x | exists j: int :: 0 <= j < |s| && s[j] == x
}

{:fuel 30}
ghost function UniqueProd(s: seq<int>): int
{
  if |s| == 0 then 1
  else
    var x := s[|s|-1];
    var pre := s[..|s|-1];
    if x in Seen(pre) then UniqueProd(pre) else UniqueProd(pre) * x
}

lemma SeenExtend(s: seq<int>, x: int)
  ensures Seen(s + [x]) == Seen(s) + {x}
{
  assert forall y :: y in Seen(s + [x]) <==> y in Seen(s) + {x} by
  {
    intro y;
    if y in Seen(s + [x]) {
      assert exists j: int :: 0 <= j < |s + [x]| && (s + [x])[j] == y;
      var j :| 0 <= j < |s + [x]| && (s + [x])[j] == y;
      if j < |s| {
        assert s[j] == y;
        assert y in Seen(s);
        assert y in Seen(s) + {x};
      } else {
        assert j == |s|;
        assert (s + [x])[|s|] == x;
        assert y == x;
        assert y in {x};
        assert y in Seen(s) + {x};
      }
    } else {
      if y in Seen(s) + {x} {
        if y in Seen(s) {
          assert exists j: int :: 0 <= j < |s| && s[j] == y;
          var j :| 0 <= j < |s| && s[j] == y;
          assert 0 <= j < |s + [x]|;
          assert (s + [x])[j] == y;
          assert y in Seen(s + [x]);
        } else {
          assert y in {x};
          assert y == x;
          assert 0 <= |s| < |s + [x]|;
          assert (s + [x])[|s|] == x;
          assert y in Seen(s + [x]);
        }
      }
    }
  }
}

lemma UniqueProdExtend(s: seq<int>, x: int)
  ensures UniqueProd(s + [x]) == (if x in Seen(s) then UniqueProd(s) else UniqueProd(s) * x)
{
}

method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == UniqueProd(a[..a.Length])
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant seen == Seen(a[..i])
      invariant product == UniqueProd(a[..i])
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            product := product * a[i];
            SeenExtend(a[..i], a[i]);
            assert Seen(a[..i+1]) == Seen(a[..i] + [a[i]]);
            assert seen == Seen(a[..i+1]);
            UniqueProdExtend(a[..i], a[i]);
            assert product == UniqueProd(a[..i+1]);
        } else {
            SeenExtend(a[..i], a[i]);
            assert Seen(a[..i+1]) == Seen(a[..i] + [a[i]]);
            assert seen == Seen(a[..i+1]);
            UniqueProdExtend(a[..i], a[i]);
            assert product == UniqueProd(a[..i+1]);
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
