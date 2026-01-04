
// Corrected the function IsSubsequence to use the correct definition of subsequence
ghost function IsSubsequence<T>(s1: seq<T>, s2: seq<T>): bool {
  exists i: seq<int> :: |i| == |s1| && increasing(i) && forall j :: 0 <= j < |s1| ==> 0 <= i[j] < |s2| && s1[j] == s2[i[j]]
}

// Helper function to check if a sequence of integers is in increasing order
ghost function increasing(s: seq<int>): bool {
  forall i :: 0 <= i < |s|-1 ==> s[i] < s[i+1]
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
    invariant IsSubsequence(diff, a[..i])
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


