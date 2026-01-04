// Returns a sequence with all the duplicates removed from the input sequence
// (keeping the first occurrence of each element).
function {:fuel 10} RD<T(==)>(s: seq<T>): seq<T>
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

lemma InAppend<T>(s: seq<T>, y: T, x: T)
  ensures (x in s + [y]) <==> (x in s || x == y)
{
  // -> direction
  if x in s + [y] {
    var k :| 0 <= k < |s + [y]| && (s + [y])[k] == x;
    if k < |s| {
      assert x in s;
    } else {
      assert k == |s|;
      assert (s + [y])[|s|] == y;
      assert x == y;
    }
  }

  // <- direction
  if x in s {
    var k :| 0 <= k < |s| && s[k] == x;
    assert 0 <= k < |s + [y]|;
    assert (s + [y])[k] == x;
  } else if x == y {
    assert 0 <= |s| < |s + [y]|;
    assert (s + [y])[|s|] == y;
  }
}

lemma NoDupsAppendFresh<T(==)>(s: seq<T>, x: T)
  requires NoDups(s)
  requires x !in s
  ensures NoDups(s + [x])
{
  assert forall i, j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] != (s + [x])[j];
  forall i, j | 0 <= i < j < |s + [x]| ensures (s + [x])[i] != (s + [x])[j] {
    if j < |s| {
      // both in old part
      assert (s + [x])[i] == s[i];
      assert (s + [x])[j] == s[j];
      assert s[i] != s[j];
    } else {
      // j is the last index |s|
      assert j == |s|;
      assert i < |s|;
      assert (s + [x])[i] == s[i];
      assert (s + [x])[j] == x;
      assert s[i] != x;
    }
  }
}

lemma RD_Membership<T(==)>(s: seq<T>, x: T)
  ensures (x in RD(s)) <==> (x in s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var s0 := s[..|s|-1];
    var last := s[|s|-1];

    RD_Membership(s0, x);
    RD_Membership(s0, last);

    var t := RD(s0);

    if last in t {
      // RD(s) == t
      assert RD(s) == t;

      // last in t  <->  last in s0  (by IH with x=last)
      assert last in s0;

      // x in s  <->  x in s0 (since last already occurred in s0)
      InAppend(s0, last, x);
      assert (x in s) <==> (x in s0 || x == last);
      if x == last {
        assert x in s0;
      }
      assert (x in s) <==> (x in s0);

      // and x in t <-> x in s0 (IH with x)
      assert (x in t) <==> (x in s0);
      assert (x in RD(s)) <==> (x in s);
    } else {
      // RD(s) == t + [last]
      assert RD(s) == t + [last];

      // last !in t  <->  last !in s0 (by IH with x=last)
      assert last !in s0;

      InAppend(t, last, x);
      InAppend(s0, last, x);

      // Use IH: (x in t) <-> (x in s0)
      assert (x in t) <==> (x in s0);

      // Combine the append characterizations
      assert (x in RD(s)) <==> (x in t || x == last);
      assert (x in s) <==> (x in s0 || x == last);
      assert (x in RD(s)) <==> (x in s);
    }
  }
}

lemma RD_NoDups<T(==)>(s: seq<T>)
  ensures NoDups(RD(s))
  decreases |s|
{
  if |s| == 0 {
  } else {
    var s0 := s[..|s|-1];
    var last := s[|s|-1];
    RD_NoDups(s0);
    var t := RD(s0);

    if last in t {
      assert RD(s) == t;
    } else {
      assert RD(s) == t + [last];
      RD_Membership(s0, last);
      assert last !in s0;
      RD_Membership(s0, last);
      assert last !in t;
      NoDupsAppendFresh(t, last);
    }
  }
}

lemma RDAppendNew<T(==)>(s: seq<T>, x: T)
  requires x !in s
  ensures RD(s + [x]) == RD(s) + [x]
{
  RD_Membership(s, x);
  assert x !in RD(s);

  // Unfold RD on (s + [x])
  assert (s + [x])[..|(s + [x])|-1] == s;
  assert (s + [x])[|(s + [x])|-1] == x;

  assert RD(s + [x]) == (if x in RD(s) then RD(s) else RD(s) + [x]);
  assert RD(s + [x]) == RD(s) + [x];
}

lemma RDAppendOld<T(==)>(s: seq<T>, x: T)
  requires x in s
  ensures RD(s + [x]) == RD(s)
{
  RD_Membership(s, x);
  assert x in RD(s);

  // Unfold RD on (s + [x])
  assert (s + [x])[..|(s + [x])|-1] == s;
  assert (s + [x])[|(s + [x])|-1] == x;

  assert RD(s + [x]) == (if x in RD(s) then RD(s) else RD(s) + [x]);
  assert RD(s + [x]) == RD(s);
}

method RemoveDuplicates<T(==)>(a: array<T>) returns (res: seq<T>)
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
      NoDupsAppendFresh(RD(a[..i]), a[i]);
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

