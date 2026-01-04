// Given a list s = [e1, e2, ...] and an element x,
// returns a new list [x, e1, x, e2, ...].
method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i+1] == s[i]
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2*j] == x && v[2*j+1] == s[j]
  {
    v := v + [x, s[i]];
  }
}

// Test cases checked statically
method InsertBeforeEachTest(){
  var res1 := InsertBeforeEach(["Red", "Green", "Black"], "c");
  // Help Dafny use the postcondition (quantified) to derive concrete equalities
  assert |res1| == 6;
  assert res1[0] == "c" && res1[1] == "Red";
  assert res1[2] == "c" && res1[3] == "Green";
  assert res1[4] == "c" && res1[5] == "Black";
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert |res2| == 4;
  assert res2[0] == "program" && res2[1] == "python";
  assert res2[2] == "program" && res2[3] == "java";
  assert res2 == ["program", "python", "program", "java"];
}
