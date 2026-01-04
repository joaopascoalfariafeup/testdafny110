// Returns the subsequence of elements of sequence 'a' that do not exist
// in a sequence 'b'.
method Difference<T(==)>(a: seq<T>, b: seq<T>) returns (diff: seq<T>)
  ensures |diff| <= |a|
  ensures forall i :: 0 <= i < |diff| ==> diff[i] in a
  ensures forall i :: 0 <= i < |diff| ==> diff[i] !in b
  ensures forall x :: x in diff ==> x in a && x !in b
  ensures forall x :: x in a && x !in b ==> x in diff
  // Additional postcondition to ensure ordering is preserved
  ensures diff == seqc(a, (x: T) => x !in b, (x: T) => x)
{
  diff := [];
  for i := 0 to |a|
    invariant |diff| <= i
    invariant forall k :: 0 <= k < |diff| ==> diff[k] in a[..i]
    invariant forall k :: 0 <= k < |diff| ==> diff[k] !in b
    invariant forall x :: x in diff ==> x in a[..i] && x !in b
    invariant forall x :: x in a[..i] && x !in b ==> x in diff
    // Additional invariant to ensure ordering is preserved
    invariant diff == seqc(a[..i], (x: T) => x !in b, (x: T) => x)
  {
    if a[i] !in b {
      diff := diff + [a[i]];
    }
  }
}

// Auxiliary ghost function to compute the filtered sequence preserving order
ghost function seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U>
{
  if s == [] then []
  else if f(s[|s|-1]) then seqc(s[..|s|-1], f, g) + [g(s[|s|-1])]
  else seqc(s[..|s|-1], f, g)
}

// Teste cases checked statically.
method DifferenceTest(){
  var a1:seq<int> := [1, 2, 3, 4];
  var a2:seq<int> := [2, 4, 6];
  var res1 := Difference(a1, a2);
  // Helper assertions to help Dafny verify the test
  assert a1[..] == [1, 2, 3, 4];
  assert a2[..] == [2, 4, 6];
  assert res1 == [1, 3];

  var a3: seq<int>:= [1, 2, 3, 4];
  var a4: seq<int>:= [6, 7, 1];
  var res2 := Difference(a3, a4);
  assert a3[..] == [1, 2, 3, 4];
  assert a4[..] == [6, 7, 1];
  assert res2 == [2, 3, 4];

  var a5:seq<int>:= [1, 2, 3];
  var a6:seq<int>:= [3, 2, 1];
  var res3 := Difference(a5, a6);
  assert a5[..] == [1, 2, 3];
  assert a6[..] == [3, 2, 1];
  assert res3 == [];
}
