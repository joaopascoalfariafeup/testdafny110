// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.

function {:fuel 10} InterSpec<T(==)>(a: seq<T>, b: seq<T>): seq<T>
{
  if |a| == 0 then []
  else
    var pref := InterSpec(a[..|a|-1], b);
    if a[|a|-1] in b && a[|a|-1] !in pref then pref + [a[|a|-1]] else pref
}

lemma InterSpecExtend<T(==)>(s: seq<T>, b: seq<T>, x: T)
  ensures InterSpec(s + [x], b) == (if x in b && x !in InterSpec(s, b) then InterSpec(s, b) + [x] else InterSpec(s, b))
{
}

method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == InterSpec(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == InterSpec(a[..i], b[..])
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
    }
    assert a[..(i+1)] == a[..i] + [a[i]];
    calc {
      InterSpec(a[..(i+1)], b[..]);
      == { assert a[..(i+1)] == a[..i] + [a[i]]; }
      InterSpec(a[..i] + [a[i]], b[..]);
      == { InterSpecExtend(a[..i], b[..], a[i]); }
      if a[i] in b[..] && a[i] !in InterSpec(a[..i], b[..]) then InterSpec(a[..i], b[..]) + [a[i]] else InterSpec(a[..i], b[..]);
    }
  }
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert res3 == [1, 3] || res3 == [3, 1];
}
