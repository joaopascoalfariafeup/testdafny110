// Returns the subsequence of elements of sequence 'a' that do not exist
// in a sequence 'b'.
method Difference<T(==)>(a: seq<T>, b: seq<T>) returns (diff: seq<T>)
  ensures diff == filter(a, (x) => x !in b)
{
  diff := [];
  for i := 0 to |a|
    invariant diff == filter(a[..i], (x) => x !in b)
  {
    if a[i] !in b {
      diff := diff + [a[i]];
    }
    assert a[..i+1] == a[..i] + [a[i]]; // proof helper
  }
  assert a == a[..|a|]; // proof helper
}

// Returns the subsequence of elements of 'a' that satisfy a predicate 'p'.
ghost function {:fuel 3} filter<T>(a: seq<T>, p: (T) -> bool) : seq<T> {
  if |a| == 0 then a
  else if p(a[|a| - 1]) then filter(a[..|a| - 1], p) + [a[|a| - 1]]
  else filter(a[..|a| - 1], p)
}

// Teste cases checked statically.
method DifferenceTest(){
  var a1:seq<int> := [1, 2, 3, 4];
  var a2:seq<int> := [2, 4, 6];
  var res1 := Difference(a1, a2);
  assert res1 == [1, 3];

  var a3: seq<int>:= [1, 2, 3, 4];
  var a4: seq<int>:= [6, 7, 1];
  var res2 := Difference(a3, a4);
  assert res2 == [2, 3, 4];

  var a5:seq<int>:= [1, 2, 3];
  var a6:seq<int>:= [3, 2, 1];
  var res3 := Difference(a5, a6);
  assert res3 == [];
}
