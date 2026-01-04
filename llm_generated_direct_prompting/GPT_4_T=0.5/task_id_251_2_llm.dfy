// Given a list s = [e1, e2, ...] and an element x, 
// returns a new list [x, e1, x, e2, ...].
method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  requires true
  ensures |v| == 2 * |s|
  ensures forall k :: 0 <= k < |s| ==> (v[2*k] == x && v[2*k+1] == s[k])
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall k :: 0 <= k < i ==> (v[2*k] == x && v[2*k+1] == s[k])
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
