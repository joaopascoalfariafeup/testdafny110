// Given a list s = [e1, e2, ...] and an element x,
// returns a new list [x, e1, x, e2, ...].

function {:fuel 20} InsertBeforeEachSpec<T>(s: seq<T>, x: T): seq<T>
{
  if |s| == 0 then []
  else InsertBeforeEachSpec(s[..|s|-1], x) + [x, s[|s|-1]]
}

lemma SliceAppend<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
{
}

lemma InsertBeforeEachSpecSnoc<T>(t: seq<T>, a: T, x: T)
  ensures InsertBeforeEachSpec(t + [a], x) == InsertBeforeEachSpec(t, x) + [x, a]
{
  calc {
    InsertBeforeEachSpec(t + [a], x);
    == {
      assert |t + [a]| > 0;
      assert (t + [a])[..|(t + [a])|-1] == t;
      assert (t + [a])[|(t + [a])|-1] == a;
    }
    InsertBeforeEachSpec((t + [a])[..|(t + [a])|-1], x) + [x, (t + [a])[|(t + [a])|-1]];
    == { }
    InsertBeforeEachSpec(t, x) + [x, a];
  }
}

method InsertBeforeEach<T>(s: seq<T>, x: T) returns (v: seq<T>)
  ensures v == InsertBeforeEachSpec(s, x)
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v == InsertBeforeEachSpec(s[..i], x)
  {
    // help the verifier relate the iterative append to the spec’s “snoc” recursion
    assert s[..i+1] == s[..i] + [s[i]] by { SliceAppend(s, i); };

    calc {
      v + [x, s[i]];
      == { }
      InsertBeforeEachSpec(s[..i], x) + [x, s[i]];
      == { InsertBeforeEachSpecSnoc(s[..i], s[i], x); }
      InsertBeforeEachSpec(s[..i] + [s[i]], x);
      == { }
      InsertBeforeEachSpec(s[..i+1], x);
    }
    v := v + [x, s[i]];
  }

  assert s[..|s|] == s;
}

// Test cases checked statically
method InsertBeforeEachTest() {
  var res1 := InsertBeforeEach(["Red", "Green", "Black"], "c");
  assert res1 == ["c", "Red", "c", "Green", "c", "Black"];

  var res2 := InsertBeforeEach(["python", "java"], "program");
  assert res2 == ["program", "python", "program", "java"];
}
