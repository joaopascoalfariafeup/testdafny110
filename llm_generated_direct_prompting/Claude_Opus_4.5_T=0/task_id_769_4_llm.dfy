// Returns the subsequence of elements of sequence 'a' that do not exist
// in a sequence 'b'.
ghost function DiffSeq<T(==)>(a: seq<T>, b: seq<T>): seq<T>
{
  if |a| == 0 then []
  else if a[|a|-1] in b then DiffSeq(a[..|a|-1], b)
  else DiffSeq(a[..|a|-1], b) + [a[|a|-1]]
}

method Difference<T(==)>(a: seq<T>, b: seq<T>) returns (diff: seq<T>)
  ensures diff == DiffSeq(a, b)
{
  diff := [];
  for i := 0 to |a|
    invariant diff == DiffSeq(a[..i], b)
  {
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] !in b {
      diff := diff + [a[i]];
    }
  }
  assert a[..|a|] == a;
}


// Teste cases checked statically.
method {:fuel DiffSeq<int>,5} DifferenceTest(){
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

