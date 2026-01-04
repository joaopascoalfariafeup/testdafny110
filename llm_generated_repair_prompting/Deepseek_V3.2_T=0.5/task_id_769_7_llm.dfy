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
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
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
    i := i + 1;
  }
}

// Auxiliary ghost function to compute the filtered sequence preserving order
ghost function {:fuel 10} seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U>
  ensures |seqc(s, f, g)| <= |s|
  ensures forall i :: 0 <= i < |seqc(s, f, g)| ==> exists k :: 0 <= k < |s| && f(s[k]) && seqc(s, f, g)[i] == g(s[k])
  ensures forall i :: 0 <= i < |s| && f(s[i]) ==> g(s[i]) in seqc(s, f, g)
  ensures forall i, j :: 0 <= i < j < |s| && f(s[i]) && f(s[j]) ==> 
      index_of(seqc(s, f, g), g(s[i])) < index_of(seqc(s, f, g), g(s[j]))
  ensures forall i, j :: 0 <= i < j < |seqc(s, f, g)| ==> 
      exists k, l :: 0 <= k < l < |s| && f(s[k]) && f(s[l]) && seqc(s, f, g)[i] == g(s[k]) && seqc(s, f, g)[j] == g(s[l])
  ensures s == [] ==> seqc(s, f, g) == []
  ensures s != [] ==> seqc(s, f, g) == seqc(s[..|s|-1], f, g) + (if f(s[|s|-1]) then [g(s[|s|-1])] else [])
{
  if s == [] then []
  else 
    var prev := seqc(s[..|s|-1], f, g);
    if f(s[|s|-1]) then prev + [g(s[|s|-1])]
    else prev
}

// Helper function to find index in seqc result
ghost function index_of<T>(s: seq<T>, val: T): int
  requires val in s
  ensures 0 <= index_of(s, val) < |s|
  ensures s[index_of(s, val)] == val
  ensures forall i :: 0 <= i < index_of(s, val) ==> s[i] != val
{
  if s[0] == val then 0 else 1 + index_of(s[1..], val)
}

// Teste cases checked statically.
method DifferenceTest(){
  var a1:seq<int> := [1, 2, 3, 4];
  var a2:seq<int> := [2, 4, 6];
  var res1 := Difference(a1, a2);
  // Helper assertions to help Dafny verify the test
  assert a1[..] == [1, 2, 3, 4];
  assert a2[..] == [2, 4, 6];
  // Prove seqc computation for this specific case
  calc {
    seqc([1,2,3,4], (x: int) => x !in [2,4,6], (x: int) => x);
    seqc([1,2,3], (x: int) => x !in [2,4,6], (x: int) => x) + (if 4 !in [2,4,6] then [4] else []);
    seqc([1,2], (x: int) => x !in [2,4,6], (x: int) => x) + (if 3 !in [2,4,6] then [3] else []) + [];
    seqc([1], (x: int) => x !in [2,4,6], (x: int) => x) + (if 2 !in [2,4,6] then [2] else []) + [3];
    seqc([], (x: int) => x !in [2,4,6], (x: int) => x) + (if 1 !in [2,4,6] then [1] else []) + [] + [3];
    [] + [1] + [] + [3];
    [1,3];
  }
  assert res1 == [1, 3];

  var a3: seq<int>:= [1, 2, 3, 4];
  var a4: seq<int>:= [6, 7, 1];
  var res2 := Difference(a3, a4);
  assert a3[..] == [1, 2, 3, 4];
  assert a4[..] == [6, 7, 1];
  // Prove seqc computation for this specific case
  calc {
    seqc([1,2,3,4], (x: int) => x !in [6,7,1], (x: int) => x);
    seqc([1,2,3], (x: int) => x !in [6,7,1], (x: int) => x) + (if 4 !in [6,7,1] then [4] else []);
    seqc([1,2], (x: int) => x !in [6,7,1], (x: int) => x) + (if 3 !in [6,7,1] then [3] else []) + [4];
    seqc([1], (x: int) => x !in [6,7,1], (x: int) => x) + (if 2 !in [6,7,1] then [2] else []) + [3,4];
    seqc([], (x: int) => x !in [6,7,1], (x: int) => x) + (if 1 !in [6,7,1] then [1] else []) + [2,3,4];
    [] + [] + [2,3,4];
    [2,3,4];
  }
  assert res2 == [2, 3, 4];

  var a5:seq<int>:= [1, 2, 3];
  var a6:seq<int>:= [3, 2, 1];
  var res3 := Difference(a5, a6);
  assert a5[..] == [1, 2, 3];
  assert a6[..] == [3, 2, 1];
  // Prove seqc computation for this specific case
  calc {
    seqc([1,2,3], (x: int) => x !in [3,2,1], (x: int) => x);
    seqc([1,2], (x: int) => x !in [3,2,1], (x: int) => x) + (if 3 !in [3,2,1] then [3] else []);
    seqc([1], (x: int) => x !in [3,2,1], (x: int) => x) + (if 2 !in [3,2,1] then [2] else []) + [];
    seqc([], (x: int) => x !in [3,2,1], (x: int) => x) + (if 1 !in [3,2,1] then [1] else []) + [] + [];
    [] + [] + [] + [];
    [];
  }
  assert res3 == [];
}

