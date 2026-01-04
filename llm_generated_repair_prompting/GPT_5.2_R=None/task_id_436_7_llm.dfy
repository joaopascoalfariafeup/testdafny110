// Returns the subsequence of negative elements of s, preserving order.
ghost function {:fuel 10} NegSeq(s: seq<int>): seq<int>
  ensures forall j :: 0 <= j < |NegSeq(s)| ==> NegSeq(s)[j] < 0
{
  if |s| == 0 then []
  else
    var t := NegSeq(s[..|s|-1]);
    if s[|s|-1] < 0 then t + [s[|s|-1]] else t
}

// A useful lemma that matches the loop's forward iteration with NegSeq's definition.
lemma NegSeqExtend(s: seq<int>, x: int)
  ensures NegSeq(s + [x]) == (if x < 0 then NegSeq(s) + [x] else NegSeq(s))
{
  calc {
    NegSeq(s + [x]);
    == { }
    if (s + [x])[|s + [x]| - 1] < 0
      then NegSeq((s + [x])[..|s + [x]| - 1]) + [(s + [x])[|s + [x]| - 1]]
      else NegSeq((s + [x])[..|s + [x]| - 1]);
    == {
      assert |s + [x]| == |s| + 1;
      assert (s + [x])[..|s + [x]| - 1] == s;
      assert (s + [x])[|s + [x]| - 1] == x;
    }
    if x < 0 then NegSeq(s) + [x] else NegSeq(s);
  }
}

// Resturns a sequence with the negative numbers in the input array 'a',
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == NegSeq(a[..])
  ensures forall j :: 0 <= j < |res| ==> res[j] < 0
  ensures forall i :: 0 <= i < a.Length && a[i] < 0 ==> exists j :: 0 <= j < |res| && res[j] == a[i]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == NegSeq(a[..i])
    invariant forall j :: 0 <= j < |res| ==> res[j] < 0
    invariant forall k :: 0 <= k < i && a[k] < 0 ==> exists j :: 0 <= j < |res| && res[j] == a[k]
  {
    // Help Dafny relate the loop to NegSeq's recursive definition
    assert a[..i+1] == a[..i] + [a[i]];

    // Make the one-step NegSeq relationship explicit for this i
    assert NegSeq(a[..i+1]) == (if a[i] < 0 then NegSeq(a[..i]) + [a[i]] else NegSeq(a[..i]))
      by { NegSeqExtend(a[..i], a[i]); }

    if a[i] < 0 {
      // remember old res for reasoning about elements that were already included
      ghost var oldRes := res;

      res := res + [a[i]];

      // Prove the "all negatives seen so far are in res" invariant for i+1
      forall k | 0 <= k < i+1 && a[k] < 0
        ensures exists j :: 0 <= j < |res| && res[j] == a[k]
      {
        if k < i {
          // use the previous invariant on oldRes (= NegSeq(a[..i]))
          assert oldRes == NegSeq(a[..i]);
          assert exists j :: 0 <= j < |oldRes| && oldRes[j] == a[k];

          var j :| 0 <= j < |oldRes| && oldRes[j] == a[k];

          // oldRes is a prefix of res after appending one element
          assert res == oldRes + [a[i]];
          assert |res| == |oldRes| + 1;
          assert 0 <= j < |res|;
          assert res[j] == a[k];
        } else {
          assert k == i;
          assert res[|res|-1] == a[i];
        }
      }
      // Close the quantified invariant in a way Dafny can use
      assert forall k :: 0 <= k < i+1 && a[k] < 0 ==> exists j :: 0 <= j < |res| && res[j] == a[k];
    } else {
      // Prove the "all negatives seen so far are in res" invariant for i+1 (no change to res)
      forall k | 0 <= k < i+1 && a[k] < 0
        ensures exists j :: 0 <= j < |res| && res[j] == a[k]
      {
        // since a[i] is not negative, k cannot be i
        assert k < i;
        // from previous invariant
        assert exists j :: 0 <= j < |res| && res[j] == a[k];
      }
      assert forall k :: 0 <= k < i+1 && a[k] < 0 ==> exists j :: 0 <= j < |res| && res[j] == a[k];
    }
  }
}


// Test cases checked statically.
method FindNegativeNumbersTest(){
  var a1 := new int[] [-1, 4, 5, -6];
  assert a1[..] == [-1, 4, 5, -6];
  var res1 := FindNegativeNumbers(a1);
  assert res1 == [-1, -6];

  var a2:= new int[] [-1, -2, -3];
  assert a2[..] == [-1, -2, -3];
  var res2 := FindNegativeNumbers(a2);
  assert res2 == [-1, -2, -3];

  var a3:= new int[] [0, 1];
  assert a3[..] == [0, 1];
  var res3 := FindNegativeNumbers(a3);
  assert res3 == [];
}
