
ghost predicate TransitionAt(s: seq<int>, i: int)
{
  1 <= i < |s| && s[i] != s[i-1]
}

// Make finiteness obvious to Dafny by bounding i directly in the comprehension.
ghost function Transitions(s: seq<int>): set<int>
{
  set i:int | 1 <= i < |s| && s[i] != s[i-1]
}

// RunsCount is the number of maximal constant runs in the sequence.
// Defined recursively in the same direction as the loop grows prefixes.
ghost function {:fuel 5} RunsCount(s: seq<int>): nat
{
  if |s| == 0 then 0
  else if |s| == 1 then 1
  else
    (if s[|s|-1] == s[|s|-2] then RunsCount(s[..|s|-1])
     else RunsCount(s[..|s|-1]) + 1) as nat
}

lemma RunsCountSnoc(s: seq<int>, x: int)
  requires |s| > 0
  ensures RunsCount(s + [x]) ==
            (if x == s[|s|-1] then RunsCount(s) else RunsCount(s) + 1)
{
  // Let t = s + [x]; then |t| >= 2, so unfold RunsCount(t) once.
  assert |s + [x]| == |s| + 1;
  assert |s + [x]| >= 2;
  calc {
    RunsCount(s + [x]);
    ==
    (if (s + [x])[|s + [x]| - 1] == (s + [x])[|s + [x]| - 2]
     then RunsCount((s + [x])[..|s + [x]| - 1])
     else RunsCount((s + [x])[..|s + [x]| - 1]) + 1) as nat;
    ==
    (if x == s[|s|-1]
     then RunsCount(s)
     else RunsCount(s) + 1) as nat;
  }
}

lemma SeqSliceAll<T>(s: seq<T>)
  ensures s[..|s|] == s
{
}

method CountDistinct(a: array<int>) returns (count: nat)
  ensures count == RunsCount(a[..])
  ensures count <= a.Length
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;

    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= count <= i
      invariant count == RunsCount(a[..i])
    {
        // Help Dafny relate the next prefix to snoc
        assert a[..i+1] == a[..i] + [a[i]];

        if a[i] != a[i-1] {
            count := count + 1;
        } else {
        }

        // Re-establish the main invariant for the next i
        assert count == RunsCount(a[..i] + [a[i]]) by {
          RunsCountSnoc(a[..i], a[i]);
        }
        assert count == RunsCount(a[..i+1]);
    }

    // Bridge the loop-exit invariant (i == a.Length) to the method postcondition
    assert count == RunsCount(a[..a.Length]);
    SeqSliceAll(a[..]);
    assert a[..a.Length] == a[..];
    assert count == RunsCount(a[..]);

    return count;
}

method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}

