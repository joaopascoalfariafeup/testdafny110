// Returns a sequence with all elements belonging to the first array
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
function {:fuel 20} ExpRemoveElements<T(==)>(a: seq<T>, b: seq<T>, i: nat): seq<T>
  requires i <= |a|
  decreases i
{
  if i == 0 then
    []
  else
    var j := i - 1;
    var prev := ExpRemoveElements(a, b, j);
    if a[j] !in b && a[j] !in a[..j] then prev + [a[j]] else prev
}

// Helpful one-step unfolding lemma for calculations/proofs
lemma ExpRemoveElementsStep<T(==)>(a: seq<T>, b: seq<T>, i: nat)
  requires 0 < i <= |a|
  ensures ExpRemoveElements(a, b, i) ==
            (if a[i-1] !in b && a[i-1] !in a[..i-1]
             then ExpRemoveElements(a, b, i-1) + [a[i-1]]
             else ExpRemoveElements(a, b, i-1))
{
}

method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == ExpRemoveElements(a[..], b[..], a.Length)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == ExpRemoveElements(a[..], b[..], i as nat)
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
}




// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);

  // Help the verifier with concrete slices
  assert a1[..] == [1, 2, 3, 4];
  assert a2[..] == [2, 4];

  // Compute the expected value by unfolding ExpRemoveElements
  var s := a1[..];
  var t := a2[..];

  // i = 4 (element 4 is in t, so skipped)
  assert s[3] == 4;
  assert 4 in t;
  calc {
    ExpRemoveElements(s, t, 4);
    == { ExpRemoveElementsStep(s, t, 4); }
    (if s[3] !in t && s[3] !in s[..3] then ExpRemoveElements(s, t, 3) + [s[3]] else ExpRemoveElements(s, t, 3));
    == { assert !(s[3] !in t && s[3] !in s[..3]); }
    ExpRemoveElements(s, t, 3);
  }

  // i = 3 (element 3 is kept)
  assert s[2] == 3;
  assert 3 !in t;
  assert s[..2] == [1, 2];
  assert 3 !in s[..2];
  calc {
    ExpRemoveElements(s, t, 3);
    == { ExpRemoveElementsStep(s, t, 3); }
    (if s[2] !in t && s[2] !in s[..2] then ExpRemoveElements(s, t, 2) + [s[2]] else ExpRemoveElements(s, t, 2));
    == { assert (s[2] !in t && s[2] !in s[..2]); }
    ExpRemoveElements(s, t, 2) + [3];
  }

  // i = 2 (element 2 is in t, so skipped)
  assert s[1] == 2;
  assert 2 in t;
  calc {
    ExpRemoveElements(s, t, 2);
    == { ExpRemoveElementsStep(s, t, 2); }
    (if s[1] !in t && s[1] !in s[..1] then ExpRemoveElements(s, t, 1) + [s[1]] else ExpRemoveElements(s, t, 1));
    == { assert !(s[1] !in t && s[1] !in s[..1]); }
    ExpRemoveElements(s, t, 1);
  }

  // i = 1 (element 1 is kept)
  assert s[0] == 1;
  assert 1 !in t;
  assert s[..0] == [];
  assert 1 !in s[..0];
  calc {
    ExpRemoveElements(s, t, 1);
    == { ExpRemoveElementsStep(s, t, 1); }
    (if s[0] !in t && s[0] !in s[..0] then ExpRemoveElements(s, t, 0) + [s[0]] else ExpRemoveElements(s, t, 0));
    == { assert (s[0] !in t && s[0] !in s[..0]); }
    ExpRemoveElements(s, t, 0) + [1];
    == { }
    [] + [1];
    == { }
    [1];
  }

  // Put it together: ExpRemoveElements(s,t,4) == [1,3]
  calc {
    ExpRemoveElements(s, t, 4);
    == { }
    ExpRemoveElements(s, t, 3);
    == { }
    ExpRemoveElements(s, t, 2) + [3];
    == { }
    ExpRemoveElements(s, t, 1) + [3];
    == { }
    [1] + [3];
    == { }
    [1, 3];
  }

  // Now conclude the test assertion
  assert res1 == ExpRemoveElements(a1[..], a2[..], a1.Length);
  assert res1 == [1, 3];
}

  // Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  assert res2 == [];
  var res3 := RemoveElements(a1, a2);
  assert res3 == [1, 2, 3, 4];
}


// Duplicates in the first array
method RemoveElementsDups(){
  var a1 := new int[] [1, 2, 1, 3];
  var a2 := new int[] [1, 2, 1, 3, 2];
  var a3 := new int[] [1];
  var res1 := RemoveElements(a1, a3);

  // Help the verifier with concrete slices
  assert a1[..] == [1, 2, 1, 3];
  assert a3[..] == [1];

  // Compute ExpRemoveElements([1,2,1,3],[1],4) = [2,3]
  var s := a1[..];
  var t := a3[..];

  // i = 4 (3 kept)
  assert s[3] == 3;
  assert 3 !in t;
  assert s[..3] == [1, 2, 1];
  assert 3 !in s[..3];
  calc {
    ExpRemoveElements(s, t, 4);
    == { ExpRemoveElementsStep(s, t, 4); }
    (if s[3] !in t && s[3] !in s[..3] then ExpRemoveElements(s, t, 3) + [s[3]] else ExpRemoveElements(s, t, 3));
    == { assert (s[3] !in t && s[3] !in s[..3]); }
    ExpRemoveElements(s, t, 3) + [3];
  }

  // i = 3 (the second 1 skipped: it is in t, and also in prefix)
  assert s[2] == 1;
  assert 1 in t;
  calc {
    ExpRemoveElements(s, t, 3);
    == { ExpRemoveElementsStep(s, t, 3); }
    (if s[2] !in t && s[2] !in s[..2] then ExpRemoveElements(s, t, 2) + [s[2]] else ExpRemoveElements(s, t, 2));
    == { assert !(s[2] !in t && s[2] !in s[..2]); }
    ExpRemoveElements(s, t, 2);
  }

  // i = 2 (2 kept)
  assert s[1] == 2;
  assert 2 !in t;
  assert s[..1] == [1];
  assert 2 !in s[..1];
  calc {
    ExpRemoveElements(s, t, 2);
    == { ExpRemoveElementsStep(s, t, 2); }
    (if s[1] !in t && s[1] !in s[..1] then ExpRemoveElements(s, t, 1) + [s[1]] else ExpRemoveElements(s, t, 1));
    == { assert (s[1] !in t && s[1] !in s[..1]); }
    ExpRemoveElements(s, t, 1) + [2];
  }

  // i = 1 (1 skipped)
  assert s[0] == 1;
  assert 1 in t;
  calc {
    ExpRemoveElements(s, t, 1);
    == { ExpRemoveElementsStep(s, t, 1); }
    (if s[0] !in t && s[0] !in s[..0] then ExpRemoveElements(s, t, 0) + [s[0]] else ExpRemoveElements(s, t, 0));
    == { assert !(s[0] !in t && s[0] !in s[..0]); }
    ExpRemoveElements(s, t, 0);
    == { }
    [];
  }

  calc {
    ExpRemoveElements(s, t, 4);
    == { }
    ExpRemoveElements(s, t, 3) + [3];
    == { }
    ExpRemoveElements(s, t, 2) + [3];
    == { }
    (ExpRemoveElements(s, t, 1) + [2]) + [3];
    == { }
    ([] + [2]) + [3];
    == { }
    [2, 3];
  }

  assert res1 == ExpRemoveElements(a1[..], a3[..], a1.Length);
  assert res1 == [2, 3] ;

  var res2 := RemoveElements(a2, a3);
  assert res2 == [2, 3] ;
}
