// Given a list s = [e1, e2, ...] and an element x, 
// returns a new list [x, e1, x, e2, ...].
ghost function InsertBeforeEachSpec<T>(s: seq<T>, x: T): seq<T>
{
  if |s| == 0 then []
  else InsertBeforeEachSpec(s[..|s|-1], x) + [x, s[|s|-1]]
}

method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures v == InsertBeforeEachSpec(s, x)
  ensures |v| == 2 * |s|
  ensures forall k :: 0 <= k < |s| ==> v[2*k] == x && v[2*k + 1] == s[k]
{
  v := [];
  for i := 0 to |s|
    invariant v == InsertBeforeEachSpec(s[..i], x)
    invariant |v| == 2 * i
    invariant forall k :: 0 <= k < i ==> v[2*k] == x && v[2*k + 1] == s[k]
  {
    assert s[..i+1] == s[..i] + [s[i]];
    v := v + [x, s[i]];
  }
  assert s[..|s|] == s;
}

// Test cases checked statically
method InsertBeforeEachTest(){
  var res1 := InsertBeforeEach(["Red", "Green", "Black"], "c");
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert res2 == ["program", "python", "program", "java"];

}
