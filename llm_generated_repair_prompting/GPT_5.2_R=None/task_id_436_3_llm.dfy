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
  // By unfolding NegSeq on (s + [x]) once:
  //  (s+[x])[..|s+[x]|-1] == s  and  (s+[x])[|s+[x]|-1] == x
}

// Resturns a sequence with the negative numbers in the input array 'a',
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  requires a != null
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
    calc {
      NegSeq(a[..i+1]);
      == { assert a[..i+1] == a[..i] + [a[i]]; NegSeqExtend(a[..i], a[i]); }
      if a[i] < 0 then NegSeq(a[..i]) + [a[i]] else NegSeq(a[..i]);
    }

    if a[i] < 0 {
      // With a[i] < 0, NegSeq(a[..i+1]) = NegSeq(a[..i]) + [a[i]]
      res := res + [a[i]];
      assert forall k :: 0 <= k < i+1 && a[k] < 0 ==> exists j :: 0 <= j < |res| && res[j] == a[k];
    } else {
      // With a[i] >= 0, NegSeq(a[..i+1]) = NegSeq(a[..i])
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
