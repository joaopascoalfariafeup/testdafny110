
```dafny
ghost function IndexOf<T(==)>(s: seq<T>, v: T): int
  requires v in s
  ensures 0 <= IndexOf(s, v) < |s| && s[IndexOf(s, v)] == v
{
  if s[0] == v then 0 else 1 + IndexOf(s[1..], v)
}

// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures |res| <= a.Length
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..]
  ensures forall k :: 0 <= k < |res| ==> (res[k] !in res[..k])
  ensures forall k :: 0 <= k < a.Length ==> (a[k] in res[..])
  ensures forall k, j :: 0 <= k < j < a.Length ==> (a[k] == a[j] ==> IndexOf(res, a[k]) <= IndexOf(res, a[j]))
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall k :: 0 <= k < i ==> (a[k] in res[..]) 
    invariant forall k :: 0 <= k < |res| ==> (res[k] in a[..i]) 
    invariant forall k :: 0 <= k < |res| ==> (res[k] !in res[..k])
    invariant forall k, j :: 0 <= k < j < i ==> (a[k] == a[j] ==> IndexOf(res, a[k]) <= IndexOf(res, a[j]))
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
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
```

