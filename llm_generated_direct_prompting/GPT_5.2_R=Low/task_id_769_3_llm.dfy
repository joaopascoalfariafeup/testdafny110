// Returns the subsequence of elements of sequence 'a' that do not exist
// in a sequence 'b'.
function FilterNotIn<T(==)>(s: seq<T>, b: seq<T>): seq<T>
{
  if |s| == 0 then []
  else
    if s[|s|-1] in b
    then FilterNotIn(s[..|s|-1], b)
    else FilterNotIn(s[..|s|-1], b) + [s[|s|-1]]
}

lemma FilterNotInExtend<T(==)>(s: seq<T>, b: seq<T>, x: T)
  ensures FilterNotIn(s + [x], b) == (if x in b then FilterNotIn(s, b) else FilterNotIn(s, b) + [x])
{
  assert |s + [x]| == |s| + 1;
  assert (s + [x])[|s + [x]| - 1] == x;
  assert (s + [x])[..|s + [x]| - 1] == s;
}

method Difference<T(==)>(a: seq<T>, b: seq<T>) returns (diff: seq<T>)
  ensures diff == FilterNotIn(a, b)
  ensures forall x :: x in diff ==> x !in b
{
  diff := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant diff == FilterNotIn(a[..i], b)
  {
    if a[i] !in b {
      diff := diff + [a[i]];
    }

    assert a[..i] + [a[i]] == a[..i+1];
    if a[i] in b {
      calc {
        FilterNotIn(a[..i+1], b);
        == { FilterNotInExtend(a[..i], b, a[i]); }
        FilterNotIn(a[..i], b);
        == { }
        diff;
      }
    } else {
      calc {
        FilterNotIn(a[..i+1], b);
        == { FilterNotInExtend(a[..i], b, a[i]); }
        FilterNotIn(a[..i], b) + [a[i]];
        == { }
        diff;
      }
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

