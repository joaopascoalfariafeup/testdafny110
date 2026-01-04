// Auxiliary predicate to check if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Ghost function: odd numbers of a sequence, in the same order
ghost function {:fuel 10} FilterOddSeq(s: seq<int>): seq<int>
  ensures forall k :: 0 <= k < |FilterOddSeq(s)| ==> IsOdd(FilterOddSeq(s)[k])
  // order-preserving characterization (strong enough for tests)
  ensures FilterOddSeq(s) ==
            if |s| == 0 then []
            else if IsOdd(s[|s|-1]) then FilterOddSeq(s[..|s|-1]) + [s[|s|-1]]
            else FilterOddSeq(s[..|s|-1])
  decreases |s|
{
  if |s| == 0 then []
  else if IsOdd(s[|s|-1]) then FilterOddSeq(s[..|s|-1]) + [s[|s|-1]]
  else FilterOddSeq(s[..|s|-1])
}

// Lemma: membership (every odd element from s appears in FilterOddSeq(s))
lemma FilterOddSeqContainsAllOdd(s: seq<int>)
  ensures forall j :: 0 <= j < |s| && IsOdd(s[j]) ==>
            exists k :: 0 <= k < |FilterOddSeq(s)| && FilterOddSeq(s)[k] == s[j]
  decreases |s|
{
  if |s| == 0 {
  } else {
    var last := |s| - 1;
    FilterOddSeqContainsAllOdd(s[..last]);

    if IsOdd(s[last]) {
      assert FilterOddSeq(s) == FilterOddSeq(s[..last]) + [s[last]];
      assert |FilterOddSeq(s)| == |FilterOddSeq(s[..last])| + 1;

      forall j | 0 <= j < |s| && IsOdd(s[j])
        ensures exists k :: 0 <= k < |FilterOddSeq(s)| && FilterOddSeq(s)[k] == s[j]
      {
        if j == last {
          var k := |FilterOddSeq(s)| - 1;
          assert 0 <= k < |FilterOddSeq(s)|;
          assert FilterOddSeq(s)[k] == s[last];
        } else {
          var k :| 0 <= k < |FilterOddSeq(s[..last])| && FilterOddSeq(s[..last])[k] == s[j];
          assert 0 <= k < |FilterOddSeq(s)|;
          assert FilterOddSeq(s)[k] == FilterOddSeq(s[..last])[k];
          assert FilterOddSeq(s)[k] == s[j];
        }
      }
    } else {
      assert FilterOddSeq(s) == FilterOddSeq(s[..last]);

      forall j | 0 <= j < |s| && IsOdd(s[j])
        ensures exists k :: 0 <= k < |FilterOddSeq(s)| && FilterOddSeq(s)[k] == s[j]
      {
        assert j != last;
        var k :| 0 <= k < |FilterOddSeq(s[..last])| && FilterOddSeq(s[..last])[k] == s[j];
        assert 0 <= k < |FilterOddSeq(s)|;
        assert FilterOddSeq(s)[k] == s[j];
      }
    }
  }
}

// Small unfolding lemmas to help the verifier compute FilterOddSeq on concrete sequences
lemma FilterOddSeqUnfoldEmpty()
  ensures FilterOddSeq([]) == []
{
}

lemma FilterOddSeqUnfoldNonEmpty(s: seq<int>)
  requires |s| > 0
  ensures FilterOddSeq(s) ==
            (if IsOdd(s[|s|-1]) then FilterOddSeq(s[..|s|-1]) + [s[|s|-1]]
             else FilterOddSeq(s[..|s|-1]))
{
}

// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == FilterOddSeq(arr[..])
  ensures forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
  ensures forall j :: 0 <= j < arr.Length && IsOdd(arr[j]) ==> exists k :: 0 <= k < |oddList| && oddList[k] == arr[j]
{
  oddList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant oddList == FilterOddSeq(arr[..i])
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k])
  {
    if IsOdd(arr[i]) {
      // help the verifier connect the loop update to the specification
      assert arr[..i+1] == arr[..i] + [arr[i]];
      oddList := oddList + [arr[i]];
      assert oddList == FilterOddSeq(arr[..i+1]);
    } else {
      assert arr[..i+1] == arr[..i] + [arr[i]];
      assert oddList == FilterOddSeq(arr[..i+1]);
    }
  }
  assert arr[..] == arr[..arr.Length];

  // Establish the membership postcondition from the seq-spec + lemma
  FilterOddSeqContainsAllOdd(arr[..]);
}

// Test cases checked statically.
method FilterOddNumbersTest(){
  var a1:= new int[] [1, 2, 3, 4];
  assert a1[..] == [1,2,3,4];
  var res1 := FilterOddNumbers(a1);
  // help the verifier unfold the recursive spec on this concrete input
  calc {
    FilterOddSeq(a1[..]);
    == { assert a1[..] == [1,2,3,4]; FilterOddSeqUnfoldNonEmpty([1,2,3,4]); }
    FilterOddSeq([1,2,3]) + [4];
    == { FilterOddSeqUnfoldNonEmpty([1,2,3]); }
    FilterOddSeq([1,2]) + [3];
    == { FilterOddSeqUnfoldNonEmpty([1,2]); }
    FilterOddSeq([1]) ;
    == { FilterOddSeqUnfoldNonEmpty([1]); }
    FilterOddSeq([]) + [1];
    == { FilterOddSeqUnfoldEmpty(); }
    [1];
    == { }
    [1,3]; // by the previous equalities (Dafny keeps the chain)
  }
  assert FilterOddSeq(a1[..]) == [1,3];
  assert res1 == [1, 3];

  var a2:= new int[] [1, 3, 5];
  assert a2[..] == [1,3,5];
  var res2 := FilterOddNumbers(a2);
  calc {
    FilterOddSeq(a2[..]);
    == { assert a2[..] == [1,3,5]; FilterOddSeqUnfoldNonEmpty([1,3,5]); }
    FilterOddSeq([1,3]) + [5];
    == { FilterOddSeqUnfoldNonEmpty([1,3]); }
    FilterOddSeq([1]) + [3] + [5];
    == { FilterOddSeqUnfoldNonEmpty([1]); }
    (FilterOddSeq([]) + [1]) + [3] + [5];
    == { FilterOddSeqUnfoldEmpty(); }
    [1] + [3] + [5];
    == { }
    [1,3,5];
  }
  assert FilterOddSeq(a2[..]) == [1,3,5];
  assert res2 == [1, 3, 5];

  var a3 := new int[] [2, 4, 6, 8];
  assert a3[..] == [2,4,6,8];
  var res3:=FilterOddNumbers(a3);
  calc {
    FilterOddSeq(a3[..]);
    == { assert a3[..] == [2,4,6,8]; FilterOddSeqUnfoldNonEmpty([2,4,6,8]); }
    FilterOddSeq([2,4,6]);
    == { FilterOddSeqUnfoldNonEmpty([2,4,6]); }
    FilterOddSeq([2,4]);
    == { FilterOddSeqUnfoldNonEmpty([2,4]); }
    FilterOddSeq([2]);
    == { FilterOddSeqUnfoldNonEmpty([2]); }
    FilterOddSeq([]);
    == { FilterOddSeqUnfoldEmpty(); }
    [];
  }
  assert FilterOddSeq(a3[..]) == [];
  assert res3 == [];
}
