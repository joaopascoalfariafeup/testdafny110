// Ghost helpers: min/max of a non-empty sequence (used only for specs/proofs)
ghost function {:fuel 4} MinSeq(s: seq<int>): int
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

ghost function {:fuel 4} MaxSeq(s: seq<int>): int
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

// Bridge lemmas: relate MinSeq/MaxSeq on (s+[x]) to MinSeq/MaxSeq on s
lemma MinSeqExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MinSeq(s + [x]) == (if x < MinSeq(s) then x else MinSeq(s))
{
  // Unfold MinSeq on s+[x]
  assert |s + [x]| > 0;
  assert (s + [x])[..|s + [x]| - 1] == s;
}

lemma MaxSeqExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MaxSeq(s + [x]) == (if x > MaxSeq(s) then x else MaxSeq(s))
{
  // Unfold MaxSeq on s+[x]
  assert |s + [x]| > 0;
  assert (s + [x])[..|s + [x]| - 1] == s;
}

// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == MinSeq(a[..]) + MaxSeq(a[..])
  ensures exists i:int, j:int :: 0 <= i < a.Length && 0 <= j < a.Length && sum == a[i] + a[j]
  ensures forall k:int :: 0 <= k < a.Length ==> (exists j:int :: 0 <= j < a.Length && sum <= a[k] + a[j])
  ensures forall k:int :: 0 <= k < a.Length ==> (exists j:int :: 0 <= j < a.Length && a[k] + a[j] <= sum)
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal == MinSeq(a[..i])
    invariant maxVal == MaxSeq(a[..i])
  {
    if i < a.Length {
      assert a[..i+1] == a[..i] + [a[i]];
    }

    if a[i] < minVal {
      minVal := a[i];
    }
    if a[i] > maxVal {
      maxVal := a[i];
    }

    MinSeqExtend(a[..i], a[i]);
    MaxSeqExtend(a[..i], a[i]);
  }
  sum := minVal + maxVal;
}

// Concrete evaluators (avoid quantifiers / big case splits in tests)
lemma MinSeq3(s: seq<int>)
  requires |s| == 3
  ensures MinSeq(s) == (if s[0] <= s[1] && s[0] <= s[2] then s[0] else if s[1] <= s[2] then s[1] else s[2])
{
}
lemma MaxSeq3(s: seq<int>)
  requires |s| == 3
  ensures MaxSeq(s) == (if s[0] >= s[1] && s[0] >= s[2] then s[0] else if s[1] >= s[2] then s[1] else s[2])
{
}
lemma MinSeq4(s: seq<int>)
  requires |s| == 4
  ensures MinSeq(s) ==
    (if s[0] <= s[1] && s[0] <= s[2] && s[0] <= s[3] then s[0]
     else if s[1] <= s[2] && s[1] <= s[3] then s[1]
     else if s[2] <= s[3] then s[2] else s[3])
{
}
lemma MaxSeq4(s: seq<int>)
  requires |s| == 4
  ensures MaxSeq(s) ==
    (if s[0] >= s[1] && s[0] >= s[2] && s[0] >= s[3] then s[0]
     else if s[1] >= s[2] && s[1] >= s[3] then s[1]
     else if s[2] >= s[3] then s[2] else s[3])
{
}

// Test cases checked statically.
method SumMinMaxTest()
{
  var a1 := new int[] [1,2,3];
  assert a1[..] == [1,2,3];
  var out1 := SumMinMax(a1);
  // Use the method postcondition directly (avoids heavy proofs in the test)
  assert out1 == MinSeq(a1[..]) + MaxSeq(a1[..]);
  // Still keep the original concrete checks, but compute min/max via method result to avoid unfolding
  assert MinSeq(a1[..]) + MaxSeq(a1[..]) == 4;
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  assert a2[..] == [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert out2 == MinSeq(a2[..]) + MaxSeq(a2[..]);
  assert MinSeq(a2[..]) + MaxSeq(a2[..]) == 3;
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  assert a3[..] == [2,3,6];
  var out3 := SumMinMax(a3);
  assert out3 == MinSeq(a3[..]) + MaxSeq(a3[..]);
  assert MinSeq(a3[..]) + MaxSeq(a3[..]) == 8;
  assert out3 == 8;
}
