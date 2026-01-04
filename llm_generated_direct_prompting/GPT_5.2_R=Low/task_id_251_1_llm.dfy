// Given a list s = [e1, e2, ...] and an element x, 
// returns a new list [x, e1, x, e2, ...].
method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures |v| == 2 * |s|
  ensures forall j :: 0 <= j < |v| ==> v[j] == (if j % 2 == 0 then x else s[j / 2])
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < |v| ==> v[j] == (if j % 2 == 0 then x else s[j / 2])
  {
    v := v + [x, s[i]];
    assert |v| == 2 * (i + 1);
    assert v[|v| - 2] == x;
    assert v[|v| - 1] == s[i];
  }
}

// Test cases checked statically
method InsertBeforeEachTest(){
  var res1 := InsertBeforeEach(["Red", "Green", "Black"], "c");
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert res2 == ["program", "python", "program", "java"];

}
