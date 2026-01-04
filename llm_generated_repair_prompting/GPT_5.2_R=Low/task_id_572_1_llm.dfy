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
    RD_Membership(s[..|s|-1], x);
  }
}

lemma RDAppendNew<T(==)>(s: seq<T>, x: T)
  requires x !in s
  ensures RD(s + [x]) == RD(s) + [x]
{
  RD_Membership(s, x);
}

lemma RDAppendOld<T(==)>(s: seq<T>, x: T)
  requires x in s
  ensures RD(s + [x]) == RD(s)
{
  RD_Membership(s, x);
}

method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
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
      RDAppendNew(a[..i], a[i]);
      res := res + [a[i]];
      assert res == RD(a[..i+1]);
      assert NoDups(res);
    } else {
      RDAppendOld(a[..i], a[i]);
      assert res == RD(a[..i+1]);
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
