// Given a list s = [e1, e2, ...] and an element x, 
// returns a new list [x, e1, x, e2, ...].
method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
  ensures v == seqc(s, (lambda _: T -> true), (lambda e: T -> [x, e]))
{
  v := [];
  for i := 0 to |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2*j] == x && v[2*j + 1] == s[j]
    invariant v == seqc(s[..i], (lambda _: T -> true), (lambda e: T -> [x, e]))
  {
    v := v + [x, s[i]];
  }
}

ghost function seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> seq<U>): seq<U>
{
  if s == [] then []
  else if f(s[|s|-1]) then seqc(s[..|s|-1], f, g) + g(s[|s|-1])
  else seqc(s[..|s|-1], f, g)
}

// Test cases checked statically
method InsertBeforeEachTest(){
  var res1 := InsertBeforeEach(["Red", "Green", "Black"], "c");
  // Helper assertions to help Dafny verify the test
  assert |res1| == 6;
  assert forall i :: 0 <= i < 3 ==> res1[2*i] == "c" && res1[2*i + 1] == ["Red", "Green", "Black"][i];
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert |res2| == 4;
  assert forall i :: 0 <= i < 2 ==> res2[2*i] == "program" && res2[2*i + 1] == ["python", "java"][i];
  assert res2 == ["program", "python", "program", "java"];
}


