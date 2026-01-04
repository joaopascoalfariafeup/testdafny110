// Ghost specification of interleaving, defined in the same (append-at-end) order as the loop.
ghost function {:fuel 10} InterleaveSpec<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>): seq<T>
  requires |s1| == |s2| && |s1| == |s3|
  decreases |s1|
{
  if |s1| == 0 then
    []
  else
    InterleaveSpec(s1[..|s1|-1], s2[..|s2|-1], s3[..|s3|-1])
      + [s1[|s1|-1], s2[|s2|-1], s3[|s3|-1]]
}

lemma {:fuel 10} InterleaveSpecExtend<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, i: int)
  requires |s1| == |s2| && |s1| == |s3|
  requires 0 <= i < |s1|
  ensures InterleaveSpec(s1[..i+1], s2[..i+1], s3[..i+1])
        == InterleaveSpec(s1[..i],   s2[..i],   s3[..i]) + [s1[i], s2[i], s3[i]]
{
  // Let p1, p2, p3 be the (i+1)-prefixes
  var p1 := s1[..i+1];
  var p2 := s2[..i+1];
  var p3 := s3[..i+1];

  assert |p1| == i + 1;
  assert |p2| == i + 1;
  assert |p3| == i + 1;

  // Relate "drop-last" and "last" on these prefixes back to the original sequences
  assert p1[..|p1|-1] == s1[..i];
  assert p2[..|p2|-1] == s2[..i];
  assert p3[..|p3|-1] == s3[..i];

  assert p1[|p1|-1] == s1[i];
  assert p2[|p2|-1] == s2[i];
  assert p3[|p3|-1] == s3[i];

  // Unfold InterleaveSpec on the length-(i+1) prefixes
  calc {
    InterleaveSpec(p1, p2, p3);
    == {
      // since |p1| == i+1 > 0, take the non-empty branch of the definition
    }
    InterleaveSpec(p1[..|p1|-1], p2[..|p2|-1], p3[..|p3|-1]) + [p1[|p1|-1], p2[|p2|-1], p3[|p3|-1]];
    == {
      // rewrite the slices and last elements
    }
    InterleaveSpec(s1[..i], s2[..i], s3[..i]) + [s1[i], s2[i], s3[i]];
  }
}

// Interleaves the elements of three sequences (of equal length) into a single sequence.
// The result will have s1[0], s2[0], s3[0], s1[1], s2[1], s3[1], ...
method Interleave<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>) returns (r: seq<T>)
  requires |s1| == |s2|
  requires |s1| == |s3|
  ensures r == InterleaveSpec(s1, s2, s3)
  ensures |r| == 3 * |s1|
  ensures forall i :: 0 <= i < |s1| ==> r[3*i] == s1[i]
  ensures forall i :: 0 <= i < |s1| ==> r[3*i + 1] == s2[i]
  ensures forall i :: 0 <= i < |s1| ==> r[3*i + 2] == s3[i]
{
  r := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |r| == 3 * i
    invariant r == InterleaveSpec(s1[..i], s2[..i], s3[..i])
    invariant forall j :: 0 <= j < i ==> r[3*j] == s1[j]
    invariant forall j :: 0 <= j < i ==> r[3*j + 1] == s2[j]
    invariant forall j :: 0 <= j < i ==> r[3*j + 2] == s3[j]
  {
    InterleaveSpecExtend(s1, s2, s3, i);
    r := r + [s1[i], s2[i], s3[i]];
  }

  // Help Dafny rewrite the final-prefix form to the full sequences
  assert s1[..|s1|] == s1;
  assert s2[..|s2|] == s2;
  assert s3[..|s3|] == s3;
}

method InterleaveTest(){
  var s1: seq<int> := [1, 2, 3];
  var s2: seq<int> := [10, 20, 30];
  var s3: seq<int> := [100, 200, 300];
  var res1 := Interleave(s1, s2, s3);

  // Help Dafny compute the spec on this concrete input
  assert InterleaveSpec(s1, s2, s3) == [1, 10, 100, 2, 20, 200, 3, 30, 300];

  assert res1 == [1, 10, 100, 2, 20, 200, 3, 30, 300];
}
