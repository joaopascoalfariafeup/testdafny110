// Given a list s = [e1, e2, ...] and an element x, 
// returns a new list [x, e1, x, e2, ...].

ghost function InsertBeforeEachPrefix<T>(s: seq<T>, x: T, n: nat): seq<T>
  requires n <= |s|
{
  if n == 0 then []
  else InsertBeforeEachPrefix(s, x, n - 1) + [x, s[n - 1]]
}

method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures v == InsertBeforeEachPrefix(s, x, |s|)
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v == InsertBeforeEachPrefix(s, x, i)
  {
    v := v + [x, s[i]];
  }
}

// Test cases checked statically
method InsertBeforeEachTest(){
  var res1 := InsertBeforeEach(["Red", "Green", "Black"], "c");
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert res2 == ["program", "python", "program", "java"];

}
