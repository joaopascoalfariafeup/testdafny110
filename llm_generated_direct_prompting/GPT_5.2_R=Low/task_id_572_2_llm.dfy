// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
function UniqueSeq<T(==)>(s: seq<T>): seq<T>
  decreases |s|
{
  if |s| == 0 then []
  else
    var t := UniqueSeq(s[..|s|-1]);
    if s[|s|-1] in t then t else t + [s[|s|-1]]
}

lemma UniqueSeqMembership<T(==)>(s: seq<T>, x: T)
  ensures x in UniqueSeq(s) <==> x in s
  decreases |s|
{
  if |s| == 0 {
  } else {
    UniqueSeqMembership(s[..|s|-1], x);
    var t := UniqueSeq(s[..|s|-1]);
    var last := s[|s|-1];
    if last in t {
      // UniqueSeq(s) == t
      if x == last {
        assert x in UniqueSeq(s);
        assert x in s;
      } else {
        assert x in UniqueSeq(s) <==> x in t;
        assert x in s <==> x in s[..|s|-1];
      }
    } else {
      // UniqueSeq(s) == t + [last]
      if x == last {
        assert x in UniqueSeq(s);
        assert x in s;
      } else {
        assert x in (t + [last]) <==> x in t;
        assert x in s <==> x in s[..|s|-1];
      }
    }
  }
}

method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == UniqueSeq(a[..a.Length])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == UniqueSeq(a[..i])
  {
    if a[i] !in a[..i] {
      UniqueSeqMembership(a[..i], a[i]);
      assert a[i] !in res;
      res := res + [a[i]];
      assert res == UniqueSeq(a[..i] + [a[i]]);
      assert a[..i+1] == a[..i] + [a[i]];
      assert res == UniqueSeq(a[..i+1]);
    } else {
      UniqueSeqMembership(a[..i], a[i]);
      assert a[i] in res;
      assert a[..i+1] == a[..i] + [a[i]];
      assert UniqueSeq(a[..i+1]) == UniqueSeq(a[..i]);
      assert res == UniqueSeq(a[..i+1]);
    }
  }
}




// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert res2 == [1];
}
