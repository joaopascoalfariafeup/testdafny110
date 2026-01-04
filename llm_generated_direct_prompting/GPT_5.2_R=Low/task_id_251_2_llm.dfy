// Given a list s = [e1, e2, ...] and an element x, 
// returns a new list [x, e1, x, e2, ...].
function PrefixInsertBeforeEach<T>(s: seq<T>, x: T, i: nat): seq<T>
  requires i <= |s|
  decreases i
{
  if i == 0 then []
  else PrefixInsertBeforeEach(s, x, i - 1) + [x, s[i - 1]]
}

method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures v == PrefixInsertBeforeEach(s, x, |s|)
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v == PrefixInsertBeforeEach(s, x, i)
    invariant |v| == 2 * i
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
