// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
predicate NoDuplicates<T(==)>(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function UniqueFirsts<T(==)>(s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else
    var t := UniqueFirsts(s[..|s|-1]);
    if s[|s|-1] in t then t else t + [s[|s|-1]]
}

lemma UniqueFirstsSnoc<T(==)>(s: seq<T>, x: T)
  ensures UniqueFirsts(s + [x]) == (if x in s then UniqueFirsts(s) else UniqueFirsts(s) + [x])
{
}

method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == UniqueFirsts(a[..])
  ensures NoDuplicates(res)
  ensures forall x :: x in res <==> x in a[..]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == UniqueFirsts(a[..i])
    invariant NoDuplicates(res)
    invariant forall x :: x in res <==> x in a[..i]
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
    assert UniqueFirsts(a[..(i+1)]) == (if a[i] in a[..i] then UniqueFirsts(a[..i]) else UniqueFirsts(a[..i]) + [a[i]]);
    UniqueFirstsSnoc(a[..i], a[i]);
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
