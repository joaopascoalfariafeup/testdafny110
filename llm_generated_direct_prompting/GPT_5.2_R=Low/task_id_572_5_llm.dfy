// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
predicate NoDuplicates<T(==)>(s: seq<T>)
{
  forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function {:fuel 20} RemoveDupsPrefix<T(==)>(s: seq<T>, n: nat): seq<T>
  requires n <= |s|
  decreases n
{
  if n == 0 then []
  else
    var r := RemoveDupsPrefix(s, n - 1);
    if s[n - 1] in s[..n - 1] then r else r + [s[n - 1]]
}

method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == RemoveDupsPrefix(a[..], a.Length)
  ensures NoDuplicates(res)
  ensures forall x: T :: x in res ==> x in a[..]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == RemoveDupsPrefix(a[..], i)
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
    assert res == RemoveDupsPrefix(a[..], i + 1);
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
