// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
function RD<T(==)>(s: seq<T>): seq<T>
  decreases |s|
{
  if |s| == 0 then
    []
  else
    var t := RD(s[..|s|-1]);
    if s[|s|-1] in t then t else t + [s[|s|-1]]
}

predicate NoDups<T(==)>(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma RD_Membership<T(==)>(s: seq<T>, x: T)
  ensures (x in RD(s)) <==> (x in s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var last := s[|s|-1];
    RD_Membership(s[..|s|-1], x);

    var t := RD(s[..|s|-1]);

    // Use the definition of RD at s
    if last in t {
      // RD(s) == t
      // Need: x in t <==> x in s
      // But s == s[..|s|-1] + [last] and last is already in t
      if x in RD(s) {
        // x in t
      } else {
      }
    } else {
      // RD(s) == t + [last]
      if x == last {
      } else {
      }
    }
  }
}

lemma RD_NoDups<T(==)>(s: seq<T>)
  ensures NoDups(RD(s))
  decreases |s|
{
  if |s| == 0 {
  } else {
    RD_NoDups(s[..|s|-1]);
    var t := RD(s[..|s|-1]);
    var last := s[|s|-1];
    if last in t {
      // RD(s) == t
    } else {
      // RD(s) == t + [last]
      // show last is fresh in t
      RD_Membership(s[..|s|-1], last);
      assert last !in t;

      // NoDups(t + [last])
      assert NoDups(t);
      assert forall i, j :: 0 <= i < j < |t + [last]| ==> (t + [last])[i] != (t + [last])[j];
    }
  }
}

lemma RDAppendNew<T(==)>(s: seq<T>, x: T)
  requires x !in s
  ensures RD(s + [x]) == RD(s) + [x]
{
  RD_Membership(s, x);
  assert x !in RD(s);
  // Unfold RD on s+[x]
  assert (s + [x])[..|(s + [x])|-1] == s;
  assert (s + [x])[|(s + [x])|-1] == x;
}

lemma RDAppendOld<T(==)>(s: seq<T>, x: T)
  requires x in s
  ensures RD(s + [x]) == RD(s)
{
  RD_Membership(s, x);
  assert x in RD(s);
  // Unfold RD on s+[x]
  assert (s + [x])[..|(s + [x])|-1] == s;
  assert (s + [x])[|(s + [x])|-1] == x;
}

method RemoveDuplicates<T(==)>(a: array<T>) returns (res: seq<T>)
  requires a != null
  ensures res == RD(a[..])
  ensures NoDups(res)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == RD(a[..i])
    invariant NoDups(res)
  {
    if a[i] !in a[..i] {
      // connect slice with append
      assert a[..i+1] == a[..i] + [a[i]];

      // show a[i] is not already in res
      RD_Membership(a[..i], a[i]);
      assert a[i] !in RD(a[..i]);
      assert a[i] !in res;

      RDAppendNew(a[..i], a[i]);
      res := res + [a[i]];

      assert res == RD(a[..i+1]);

      // preserve NoDups after appending a fresh element
      assert NoDups(res);
    } else {
      // connect slice with append
      assert a[..i+1] == a[..i] + [a[i]];

      RDAppendOld(a[..i], a[i]);
      assert res == RD(a[..i+1]);
    }
  }

  // relate a[..] and a[..a.Length]
  assert a[..] == a[..a.Length];
}



// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  assert a1[..] == [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  assert a2[..] == [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert res2 == [1];
}
