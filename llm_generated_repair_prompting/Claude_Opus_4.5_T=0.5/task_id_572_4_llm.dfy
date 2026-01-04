// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..]
  ensures forall k :: 0 <= k < a.Length && a[k] !in a[..k] ==> a[k] in res
  ensures forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
  ensures forall k :: 0 <= k < |res| ==> exists i :: 0 <= i < a.Length && a[i] == res[k] && a[i] !in a[..i]
  ensures res == RemoveDuplicatesFunc(a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant res == RemoveDuplicatesFuncHelper(a[..], 0, i)
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k :: 0 <= k < i && a[k] !in a[..k] ==> a[k] in res
    invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
    invariant forall k :: 0 <= k < |res| ==> exists m :: 0 <= m < i && a[m] == res[k] && a[m] !in a[..m]
  {
    assert a[..i+1] == a[..i] + [a[i]];
    ExtendLemma(a[..], 0, i);
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
    HelperLemma(a[..], 0, i+1);
  }
  assert a[..a.Length] == a[..];
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
    // Base case
    assert RemoveDuplicatesFuncHelper(s, start, end) == [];
    if s[end] in s[..end] {
      assert s[start] in s[..start];
      assert RemoveDuplicatesFuncHelper(s, start, end+1) == RemoveDuplicatesFuncHelper(s, start+1, end+1);
      assert RemoveDuplicatesFuncHelper(s, start+1, end+1) == [];
    } else {
      assert s[start] !in s[..start];
      assert RemoveDuplicatesFuncHelper(s, start, end+1) == [s[start]] + RemoveDuplicatesFuncHelper(s, start+1, end+1);
      assert RemoveDuplicatesFuncHelper(s, start+1, end+1) == [];
      assert RemoveDuplicatesFuncHelper(s, start, end+1) == [s[end]];
    }
  } else if s[start] in s[..start] {
    ExtendLemma(s, start+1, end);
  } else {
    ExtendLemma(s, start+1, end);
    var rest := RemoveDuplicatesFuncHelper(s, start+1, end);
    var restExt := RemoveDuplicatesFuncHelper(s, start+1, end+1);
    if s[end] in s[..end] {
      assert restExt == rest;
      assert RemoveDuplicatesFuncHelper(s, start, end+1) == [s[start]] + restExt;
      assert RemoveDuplicatesFuncHelper(s, start, end) == [s[start]] + rest;
    } else {
      assert restExt == rest + [s[end]];
      assert RemoveDuplicatesFuncHelper(s, start, end+1) == [s[start]] + restExt;
      assert [s[start]] + restExt == [s[start]] + rest + [s[end]];
      assert RemoveDuplicatesFuncHelper(s, start, end) == [s[start]] + rest;
    }
  }
}

lemma HelperLemma<T>(s: seq<T>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures forall k :: 0 <= k < |RemoveDuplicatesFuncHelper(s, start, end)| ==> 
    RemoveDuplicatesFuncHelper(s, start, end)[k] in s[start..end]
  ensures forall k :: start <= k < end && s[k] !in s[..k] ==> 
    s[k] in RemoveDuplicatesFuncHelper(s, start, end)
  ensures forall j, k :: 0 <= j < k < |RemoveDuplicatesFuncHelper(s, start, end)| ==> 
    RemoveDuplicatesFuncHelper(s, start, end)[j] != RemoveDuplicatesFuncHelper(s, start, end)[k]
  ensures forall k :: 0 <= k < |RemoveDuplicatesFuncHelper(s, start, end)| ==> 
    exists m :: start <= m < end && s[m] == RemoveDuplicatesFuncHelper(s, start, end)[k] && s[m] !in s[..m]
  decreases end - start
{
  if start == end {
    // Base case: empty result
  } else if s[start] in s[..start] {
    HelperLemma(s, start+1, end);
  } else {
    HelperLemma(s, start+1, end);
    var rest := RemoveDuplicatesFuncHelper(s, start+1, end);
    var result := [s[start]] + rest;
    assert result == RemoveDuplicatesFuncHelper(s, start, end);
    assert s[start] in s[start..end];
    assert s[start] !in s[..start];
    // Show s[start] is not in rest
    forall k | 0 <= k < |rest|
      ensures rest[k] != s[start]
    {
      assert exists m :: start+1 <= m < end && s[m] == rest[k] && s[m] !in s[..m];
      var m :| start+1 <= m < end && s[m] == rest[k] && s[m] !in s[..m];
      if rest[k] == s[start] {
        assert s[m] == s[start];
        assert s[start] in s[..m];
        assert s[m] in s[..m];
        assert false;
      }
    }
  }
}

// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert a1[..] == [1, 2, 1, 2];
  assert RemoveDuplicatesFunc([1, 2, 1, 2]) == [1, 2];
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert a2[..] == [1, 1, 1];
  assert RemoveDuplicatesFunc([1, 1, 1]) == [1];
  assert res2 == [1];
}
