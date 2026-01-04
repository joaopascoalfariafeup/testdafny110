// Ghost helpers: min/max of a non-empty sequence (used only for specs/proofs)
ghost function {:fuel 2} MinSeq(s: seq<int>): int
  requires |s| > 0
  ensures MinSeq(s) in s
  ensures forall k :: 0 <= k < |s| ==> MinSeq(s) <= s[k]
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := MinSeq(s[..|s|-1]);
    if s[|s|-1] < m then s[|s|-1] else m
}

ghost function {:fuel 2} MaxSeq(s: seq<int>): int
  requires |s| > 0
  ensures MaxSeq(s) in s
  ensures forall k :: 0 <= k < |s| ==> s[k] <= MaxSeq(s)
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := MaxSeq(s[..|s|-1]);
    if s[|s|-1] > m then s[|s|-1] else m
}

// Bridge lemmas: relate the loop-computed min/max to MinSeq/MaxSeq on prefixes
lemma MinSeqExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MinSeq(s + [x]) == (if x < MinSeq(s) then x else MinSeq(s))
{
  // MinSeq(s+[x]) unfolds to MinSeq(s) compared with x
}

lemma MaxSeqExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MaxSeq(s + [x]) == (if x > MaxSeq(s) then x else MaxSeq(s))
{
}

// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == MinSeq(a[..]) + MaxSeq(a[..])
  // Keep the original postconditions as well (strengthen to avoid heavy existential search in tests)
  ensures exists i:int, j:int :: 0 <= i < a.Length && 0 <= j < a.Length && sum == a[i] + a[j]
  ensures forall k:int :: 0 <= k < a.Length ==> (exists j:int :: 0 <= j < a.Length && sum <= a[k] + a[j])
  ensures forall k:int :: 0 <= k < a.Length ==> (exists j:int :: 0 <= j < a.Length && a[k] + a[j] <= sum)
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    // Strong, deterministic invariants (avoid existential search/timeouts)
    invariant minVal == MinSeq(a[..i])
    invariant maxVal == MaxSeq(a[..i])
    // keep some original-style facts (cheap)
    invariant forall k:int :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k:int :: 0 <= k < i ==> a[k] <= maxVal
  {
    // helpful equalities about slices for the lemmas below
    assert a[..i+1] == a[..i] + [a[i]];

    if a[i] < minVal {
      minVal := a[i];
    }
    if a[i] > maxVal {
      maxVal := a[i];
    }

    // re-establish the strong invariants
    MinSeqExtend(a[..i], a[i]);
    MaxSeqExtend(a[..i], a[i]);
  }
  sum := minVal + maxVal;
}

// Small concrete min/max helpers to avoid expensive reasoning over MinSeq/MaxSeq in tests
lemma MinSeq3(s: seq<int>)
  requires |s| == 3
  ensures MinSeq(s) == (if s[0] <= s[1] && s[0] <= s[2] then s[0] else if s[1] <= s[2] then s[1] else s[2])
{
  // unfold MinSeq twice (by triggering slice equalities)
  assert s[..|s|-1] == [s[0], s[1]];
  assert s[..|s|-2] == [s[0]];
}

lemma MaxSeq3(s: seq<int>)
  requires |s| == 3
  ensures MaxSeq(s) == (if s[0] >= s[1] && s[0] >= s[2] then s[0] else if s[1] >= s[2] then s[1] else s[2])
{
  // unfold MaxSeq twice
  assert s[..|s|-1] == [s[0], s[1]];
  assert s[..|s|-2] == [s[0]];
}

lemma MinSeq4(s: seq<int>)
  requires |s| == 4
  ensures MinSeq(s) ==
    (if s[0] <= s[1] && s[0] <= s[2] && s[0] <= s[3] then s[0]
     else if s[1] <= s[2] && s[1] <= s[3] then s[1]
     else if s[2] <= s[3] then s[2] else s[3])
{
  // unfold MinSeq a few times
  assert s[..|s|-1] == [s[0], s[1], s[2]];
  MinSeq3(s[..|s|-1]);
}

lemma MaxSeq4(s: seq<int>)
  requires |s| == 4
  ensures MaxSeq(s) ==
    (if s[0] >= s[1] && s[0] >= s[2] && s[0] >= s[3] then s[0]
     else if s[1] >= s[2] && s[1] >= s[3] then s[1]
     else if s[2] >= s[3] then s[2] else s[3])
{
  // unfold MaxSeq a few times
  assert s[..|s|-1] == [s[0], s[1], s[2]];
  MaxSeq3(s[..|s|-1]);
}

// Test cases checked statically.
method SumMinMaxTest(){
  var a1 := new int[] [1,2,3];
  assert a1[..] == [1,2,3];
  var out1 := SumMinMax(a1);
  // Help the prover compute MinSeq/MaxSeq on this concrete array
  MinSeq3(a1[..]); MaxSeq3(a1[..]);
  assert MinSeq(a1[..]) == 1;
  assert MaxSeq(a1[..]) == 3;
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  assert a2[..] == [-1,2,3,4];
  var out2 := SumMinMax(a2);
  MinSeq4(a2[..]); MaxSeq4(a2[..]);
  assert MinSeq(a2[..]) == -1;
  assert MaxSeq(a2[..]) == 4;
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  assert a3[..] == [2,3,6];
  var out3 := SumMinMax(a3);
  MinSeq3(a3[..]); MaxSeq3(a3[..]);
  assert MinSeq(a3[..]) == 2;
  assert MaxSeq(a3[..]) == 6;
  assert out3 == 8;
}
