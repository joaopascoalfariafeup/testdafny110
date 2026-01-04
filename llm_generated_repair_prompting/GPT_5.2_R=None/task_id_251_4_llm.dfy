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
  assert forall i :: 0 <= i < 3 ==> res1[2*i] == "c" && res1[2*i+1] == ["Red", "Green", "Black"][i];

  // Instantiate the quantifier for the needed indices
  assert res1[0] == "c" && res1[1] == "Red" by { assert res1[0] == "c" && res1[1] == ["Red","Green","Black"][0]; }
  assert res1[2] == "c" && res1[3] == "Green" by { assert res1[2] == "c" && res1[3] == ["Red","Green","Black"][1]; }
  assert res1[4] == "c" && res1[5] == "Black" by { assert res1[4] == "c" && res1[5] == ["Red","Green","Black"][2]; }
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert |res2| == 4;
  assert forall i :: 0 <= i < 2 ==> res2[2*i] == "program" && res2[2*i+1] == ["python", "java"][i];

  // Instantiate the quantifier for the needed indices
  assert res2[0] == "program" && res2[1] == "python" by { assert res2[0] == "program" && res2[1] == ["python","java"][0]; }
  assert res2[2] == "program" && res2[3] == "java" by { assert res2[2] == "program" && res2[3] == ["python","java"][1]; }
  assert res2 == ["program", "python", "program", "java"];
}
