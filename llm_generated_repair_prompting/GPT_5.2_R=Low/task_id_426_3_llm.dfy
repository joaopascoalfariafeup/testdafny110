// Auxiliary predicate to checks if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Returns a sequence with the odd numbers in the input array, by the same order.
function {:fuel 10} FilterOddSeq(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if IsOdd(s[|s|-1]) then FilterOddSeq(s[..|s|-1]) + [s[|s|-1]]
  else FilterOddSeq(s[..|s|-1])
}

// Helpful one-step lemma for "snoc" (append one element)
lemma FilterOddSeqSnoc(s: seq<int>, x: int)
  ensures FilterOddSeq(s + [x]) == (if IsOdd(x) then FilterOddSeq(s) + [x] else FilterOddSeq(s))
{
  if IsOdd(x) {
    calc {
      FilterOddSeq(s + [x]);
      == { assert |s + [x]| > 0; }
      FilterOddSeq((s + [x])[..|(s + [x])|-1]) + [(s + [x])[|(s + [x])|-1]];
      == {
        assert (s + [x])[|(s + [x])|-1] == x;
        assert (s + [x])[..|(s + [x])|-1] == s;
      }
      FilterOddSeq(s) + [x];
    }
  } else {
    calc {
      FilterOddSeq(s + [x]);
      == { assert |s + [x]| > 0; }
      FilterOddSeq((s + [x])[..|(s + [x])|-1]);
      == {
        assert (s + [x])[|(s + [x])|-1] == x;
        assert (s + [x])[..|(s + [x])|-1] == s;
      }
      FilterOddSeq(s);
    }
  }
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == FilterOddSeq(arr[..])
{
  oddList := [];

  // Establish loop invariant at entry (i == 0)
  assert arr[..0] == [];
  assert FilterOddSeq(arr[..0]) == [];
  assert oddList == FilterOddSeq(arr[..0]);

  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant oddList == FilterOddSeq(arr[..i])
  {
    if IsOdd(arr[i]) {
      assert arr[..(i+1)] == arr[..i] + [arr[i]];
      FilterOddSeqSnoc(arr[..i], arr[i]);
      assert FilterOddSeq(arr[..(i+1)]) == FilterOddSeq(arr[..i]) + [arr[i]];
      oddList := oddList + [arr[i]];
      assert oddList == FilterOddSeq(arr[..(i+1)]);
    } else {
      assert arr[..(i+1)] == arr[..i] + [arr[i]];
      FilterOddSeqSnoc(arr[..i], arr[i]);
      assert FilterOddSeq(arr[..(i+1)]) == FilterOddSeq(arr[..i]);
      assert oddList == FilterOddSeq(arr[..(i+1)]);
    }
  }

  assert arr[..arr.Length] == arr[..];
}

 // Test cases checked statically.
method FilterOddNumbersTest(){
  var a1:= new int[] [1, 2, 3, 4];
  var res1 := FilterOddNumbers(a1);
  assert res1 == [1, 3];

  var a2:= new int[] [1, 3, 5];
  var res2 := FilterOddNumbers(a2);
  assert res2 == [1, 3, 5];

  var a3 := new int[] [2, 4, 6, 8];
  var res3:=FilterOddNumbers(a3);
  assert res3 == [];
}
