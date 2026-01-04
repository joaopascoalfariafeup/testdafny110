// Interleaves the elements of three sequences (of equal length) into a single sequence.
// The result will have s1[0], s2[0], s3[0], s1[1], s2[1], s3[1], ...
function InterleavePrefix<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, n: nat): seq<T>
  requires n <= |s1|
  requires |s1| == |s2|
  requires |s1| == |s3|
  decreases n
{
  if n == 0 then []
  else InterleavePrefix(s1, s2, s3, n - 1) + [s1[n - 1], s2[n - 1], s3[n - 1]]
}

function InterleaveSpec<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>): seq<T>
  requires |s1| == |s2|
  requires |s1| == |s3|
{
  InterleavePrefix(s1, s2, s3, |s1|)
}

lemma InterleavePrefixStep<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, i: nat)
  requires i < |s1|
  requires |s1| == |s2|
  requires |s1| == |s3|
  ensures InterleavePrefix(s1, s2, s3, i + 1) == InterleavePrefix(s1, s2, s3, i) + [s1[i], s2[i], s3[i]]
{
  calc {
    InterleavePrefix(s1, s2, s3, i + 1);
    == { }
    if i + 1 == 0 then [] else InterleavePrefix(s1, s2, s3, (i + 1) - 1) + [s1[(i + 1) - 1], s2[(i + 1) - 1], s3[(i + 1) - 1]];
    == { assert i + 1 != 0; }
    InterleavePrefix(s1, s2, s3, i) + [s1[i], s2[i], s3[i]];
  }
}

method Interleave<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>) returns (r: seq<T>)
  requires |s1| == |s2|
  requires |s1| == |s3|
  ensures r == InterleaveSpec(s1, s2, s3)
{
  r := [];
  for i := 0 to |s1|
    invariant r == InterleavePrefix(s1, s2, s3, i)
  {
    InterleavePrefixStep(s1, s2, s3, i);
    r := r + [s1[i], s2[i], s3[i]];
    assert r == InterleavePrefix(s1, s2, s3, i + 1);
  }
}

method InterleaveTest(){
  var s1: seq<int> := [1, 2, 3];
  var s2: seq<int> := [10, 20, 30];
  var s3: seq<int> := [100, 200, 300];
  var res1 := Interleave(s1, s2, s3);
  assert res1 == [1, 10, 100, 2, 20, 200, 3, 30, 300];
}
