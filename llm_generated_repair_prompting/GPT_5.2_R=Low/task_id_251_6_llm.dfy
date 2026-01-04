// Given a list s = [e1, e2, ...] and an element x,
// returns a new list [x, e1, x, e2, ...].

function {:fuel 20} {:opaque false} InsertBeforeEachSpec<T>(s: seq<T>, x: T): seq<T>
{
  if |s| == 0 then []
  else InsertBeforeEachSpec(s[..|s|-1], x) + [x, s[|s|-1]]
}

lemma InsertBeforeEachSpecEmpty<T>(x: T)
  ensures InsertBeforeEachSpec([], x) == []
{
  reveal InsertBeforeEachSpec;
}

lemma SliceAppend<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
{
  // Dafny's standard slice property:
  // s[..i+1] == s[..i] + s[i..i+1] and s[i..i+1] == [s[i]]
  assert s[..i+1] == s[..i] + s[i..i+1];
  assert s[i..i+1] == [s[i]];
}

lemma InsertBeforeEachSpecSnoc<T>(t: seq<T>, a: T, x: T)
  ensures InsertBeforeEachSpec(t + [a], x) == InsertBeforeEachSpec(t, x) + [x, a]
{
  reveal InsertBeforeEachSpec;

  assert |t + [a]| == |t| + 1;
  assert |t + [a]| > 0;
  assert |t + [a]| - 1 == |t|;
  assert (t + [a])[..|t|] == t;
  assert (t + [a])[|t|] == a;

  calc {
    InsertBeforeEachSpec(t + [a], x);
    == { }
    InsertBeforeEachSpec((t + [a])[..|(t + [a])|-1], x) + [x, (t + [a])[|(t + [a])|-1]];
    == {
      assert (t + [a])[..|(t + [a])|-1] == t;
      assert (t + [a])[|(t + [a])|-1] == a;
    }
    InsertBeforeEachSpec(t, x) + [x, a];
  }
}

method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures v == InsertBeforeEachSpec(s, x)
{
  v := [];

  // Establish the main invariant at loop entry (i == 0)
  assert s[..0] == [];
  assert InsertBeforeEachSpec(s[..0], x) == [] by {
    InsertBeforeEachSpecEmpty(x);
  }

  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v == InsertBeforeEachSpec(s[..i], x)
  {
    // help the verifier relate the iterative append to the spec’s “snoc” recursion
    assert s[..i+1] == s[..i] + [s[i]] by {
      SliceAppend(s, i);
    }

    calc {
      v + [x, s[i]];
      == { assert v == InsertBeforeEachSpec(s[..i], x); }
      InsertBeforeEachSpec(s[..i], x) + [x, s[i]];
      == { InsertBeforeEachSpecSnoc(s[..i], s[i], x); }
      InsertBeforeEachSpec(s[..i] + [s[i]], x);
      == { assert s[..i] + [s[i]] == s[..i+1]; }
      InsertBeforeEachSpec(s[..i+1], x);
    }
    v := v + [x, s[i]];
  }

  assert s[..|s|] == s;
}

lemma InsertBeforeEachSpecEval_RedGreenBlack()
  ensures InsertBeforeEachSpec(["Red", "Green", "Black"], "c") ==
          ["c", "Red", "c", "Green", "c", "Black"]
{
  reveal InsertBeforeEachSpec;

  calc {
    InsertBeforeEachSpec(["Red", "Green", "Black"], "c");
    == { }
    InsertBeforeEachSpec(["Red", "Green"], "c") + ["c", "Black"];
    == { }
    (InsertBeforeEachSpec(["Red"], "c") + ["c", "Green"]) + ["c", "Black"];
    == { }
    ((InsertBeforeEachSpec([], "c") + ["c", "Red"]) + ["c", "Green"]) + ["c", "Black"];
    == { }
    (([] + ["c", "Red"]) + ["c", "Green"]) + ["c", "Black"];
    == { }
    (["c", "Red"] + ["c", "Green"]) + ["c", "Black"];
    == { }
    ["c", "Red", "c", "Green"] + ["c", "Black"];
    == { }
    ["c", "Red", "c", "Green", "c", "Black"];
  }
}

lemma InsertBeforeEachSpecEval_PythonJava()
  ensures InsertBeforeEachSpec(["python", "java"], "program") ==
          ["program", "python", "program", "java"]
{
  reveal InsertBeforeEachSpec;

  calc {
    InsertBeforeEachSpec(["python", "java"], "program");
    == { }
    InsertBeforeEachSpec(["python"], "program") + ["program", "java"];
    == { }
    (InsertBeforeEachSpec([], "program") + ["program", "python"]) + ["program", "java"];
    == { }
    ([] + ["program", "python"]) + ["program", "java"];
    == { }
    ["program", "python"] + ["program", "java"];
    == { }
    ["program", "python", "program", "java"];
  }
}

// Test cases checked statically
method InsertBeforeEachTest() {
  var res1 := InsertBeforeEach(["Red", "Green", "Black"], "c");
  assert res1 == InsertBeforeEachSpec(["Red", "Green", "Black"], "c");
  assert InsertBeforeEachSpec(["Red", "Green", "Black"], "c") ==
         ["c", "Red", "c", "Green", "c", "Black"] by {
    InsertBeforeEachSpecEval_RedGreenBlack();
  }
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert res2 == InsertBeforeEachSpec(["python", "java"], "program");
  assert InsertBeforeEachSpec(["python", "java"], "program") ==
         ["program", "python", "program", "java"] by {
    InsertBeforeEachSpecEval_PythonJava();
  }
  assert res2 == ["program", "python", "program", "java"];
}
