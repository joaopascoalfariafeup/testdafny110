// Spec: subsequence of elements of 'a' that do not exist in 'b', preserving order.
ghost function {:fuel 10} SpecPrefix<T(==)>(a: seq<T>, b: seq<T>, i: int): seq<T>
  requires 0 <= i <= |a|
  decreases i
{
  if i == 0 then []
  else
    var s := SpecPrefix(a, b, i - 1);
    if a[i - 1] !in b then s + [a[i - 1]] else s
}

ghost function {:fuel 10} SpecDiff<T(==)>(a: seq<T>, b: seq<T>): seq<T>
{
  SpecPrefix(a, b, |a|)
}

// Returns the subsequence of elements of sequence 'a' that do not exist in a sequence 'b'.
method Difference<T(==)>(a: seq<T>, b: seq<T>) returns (diff: seq<T>)
  ensures diff == SpecDiff(a, b)
{
  diff := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant diff == SpecPrefix(a, b, i)
  {
    if a[i] !in b {
      diff := diff + [a[i]];
    }

    // Help the verifier re-establish the invariant for the next iteration
    if a[i] !in b {
      assert SpecPrefix(a, b, i + 1) == SpecPrefix(a, b, i) + [a[i]];
    } else {
      assert SpecPrefix(a, b, i + 1) == SpecPrefix(a, b, i);
    }
  }
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
