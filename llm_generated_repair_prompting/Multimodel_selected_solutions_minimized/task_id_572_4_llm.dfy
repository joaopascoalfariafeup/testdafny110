// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == RemoveDuplicatesFunc(a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant res == RemoveDuplicatesFuncHelper(a[..], 0, i)
  {
    ExtendLemma(a[..], 0, i);
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
}

ghost function {:fuel 5} RemoveDuplicatesFunc<T>(s: seq<T>): seq<T>
{
  RemoveDuplicatesFuncHelper(s, 0, |s|)
}

ghost function {:fuel 5} RemoveDuplicatesFuncHelper<T>(s: seq<T>, start: int, end: int): seq<T>
  requires 0 <= start <= end <= |s|
  decreases end - start
{
  if start == end then []
  else if s[start] in s[..start] then RemoveDuplicatesFuncHelper(s, start+1, end)
  else [s[start]] + RemoveDuplicatesFuncHelper(s, start+1, end)
}

lemma ExtendLemma<T>(s: seq<T>, start: int, end: int)
  requires 0 <= start <= end < |s|
  ensures s[end] in s[..end] ==> RemoveDuplicatesFuncHelper(s, start, end+1) == RemoveDuplicatesFuncHelper(s, start, end)
  ensures s[end] !in s[..end] ==> RemoveDuplicatesFuncHelper(s, start, end+1) == RemoveDuplicatesFuncHelper(s, start, end) + [s[end]]
  decreases end - start
{
  if start == end {
  } else if s[start] in s[..start] {
    ExtendLemma(s, start+1, end);
  } else {
    ExtendLemma(s, start+1, end);
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