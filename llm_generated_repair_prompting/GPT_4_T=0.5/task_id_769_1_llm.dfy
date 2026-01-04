function IsSubsequence<T(==)>(s1: seq<T>, s2: seq<T>): bool
{
  forall i :: 0 <= i < |s1| ==> s1[i] in s2
}

method Difference<T(==)>(a: seq<T>, b: seq<T>) returns (diff: seq<T>)
  ensures forall i :: 0 <= i < |a| && a[i] !in b ==> a[i] in diff
  ensures forall i :: 0 <= i < |diff| ==> diff[i] in a && diff[i] !in b
  ensures IsSubsequence(diff, a) && !IsSubsequence(diff, b)
{
  diff := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i && a[j] !in b ==> a[j] in diff
    invariant forall j :: 0 <= j < |diff| ==> diff[j] in a && diff[j] !in b
    invariant IsSubsequence(diff, a)
  {
    if a[i] !in b {
      diff := diff + [a[i]];
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

