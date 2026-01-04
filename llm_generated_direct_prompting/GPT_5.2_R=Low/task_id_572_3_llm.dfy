predicate NoDuplicates<T>(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function RemoveDupsSeq<T(==)>(s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else
    var t := RemoveDupsSeq(s[..|s|-1]);
    if s[|s|-1] in t then t else t + [s[|s|-1]]
}

lemma RemoveDupsSeq_Membership<T(==)>(s: seq<T>, x: T)
  ensures x in RemoveDupsSeq(s) <==> x in s
{
  if |s| == 0 {
  } else {
    RemoveDupsSeq_Membership(s[..|s|-1], x);
    var t := RemoveDupsSeq(s[..|s|-1]);
    if s[|s|-1] in t {
      assert RemoveDupsSeq(s) == t;
      assert x in RemoveDupsSeq(s) <==> x in t;
      assert x in t <==> x in s[..|s|-1];
      assert x in s <==> x in s[..|s|-1] || x == s[|s|-1];
      if x == s[|s|-1] {
        assert x in s[..|s|-1];
      }
    } else {
      assert RemoveDupsSeq(s) == t + [s[|s|-1]];
      assert x in (t + [s[|s|-1]]) <==> x in t || x == s[|s|-1];
      assert x in t <==> x in s[..|s|-1];
      assert x in s <==> x in s[..|s|-1] || x == s[|s|-1];
    }
  }
}

lemma RemoveDupsSeq_NoDuplicates<T(==)>(s: seq<T>)
  ensures NoDuplicates(RemoveDupsSeq(s))
{
  if |s| == 0 {
  } else {
    RemoveDupsSeq_NoDuplicates(s[..|s|-1]);
    var t := RemoveDupsSeq(s[..|s|-1]);
    if s[|s|-1] in t {
      assert RemoveDupsSeq(s) == t;
    } else {
      assert RemoveDupsSeq(s) == t + [s[|s|-1]];
      assert NoDuplicates(t + [s[|s|-1]]);
    }
  }
}

// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == RemoveDupsSeq(a[..])
  ensures NoDuplicates(res)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == RemoveDupsSeq(a[..i])
    invariant NoDuplicates(res)
  {
    if a[i] !in a[..i] {
      RemoveDupsSeq_Membership(a[..i], a[i]);
      assert a[i] !in RemoveDupsSeq(a[..i]);
      assert RemoveDupsSeq(a[..i+1]) == RemoveDupsSeq(a[..i]) + [a[i]];
      res := res + [a[i]];
    } else {
      RemoveDupsSeq_Membership(a[..i], a[i]);
      assert a[i] in RemoveDupsSeq(a[..i]);
      assert RemoveDupsSeq(a[..i+1]) == RemoveDupsSeq(a[..i]);
    }
  }
  RemoveDupsSeq_NoDuplicates(a[..]);
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
