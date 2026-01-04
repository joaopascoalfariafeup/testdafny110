// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
   ensures res == removeElems(a[..], b[..]) 
{
  res := [];
  for i := 0 to a.Length
    invariant res == removeElems(a[..i], b[..])
  {
    assert a[..i+1] == a[..i] + [a[i]]; // helper
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
  assert a[..] == a[..a.Length]; // helper
}

// Auxiliary function, defined recursively, that returns a sequence with all 
// elements belonging to 'a' that are not in 'b', by the same order, 
// without duplicates (keeping only the first occurrence).
ghost function {:fuel 4} removeElems<T(==)>(a: seq<T>, b: seq<T>): seq<T> {
  if |a| == 0 then []
  else if Last(a) !in b && Last(a) !in DropLast(a) then removeElems(DropLast(a), b) + [Last(a)]
  else removeElems(DropLast(a), b)
}

// Retrieves the same sequence with the last element removed 
ghost function DropLast<T>(s: seq<T>): seq<T>
  requires |s| > 0
{ 
  s[..|s|-1] 
}

// Retrieves the last element of a non-empty sequence
ghost function Last<T>(s: seq<T>): T
  requires |s| > 0
{ 
  s[|s|-1] 
}

// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  assert a1[..] == [1, 2, 3, 4]; //  helper
  assert a2[..] == [2, 4]; //  helper
  assert 1 in a1[..] && 1 !in a2[..]; //  helper
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
  assert a1[..] == [1, 2, 1, 3]; // proof helper
  assert a3[..] == [1]; // proof helper
  assert res1 == [2, 3] ;
  assert a2[..] == [1, 2, 1, 3, 2]; // proof helper
  assert a2[..] == a1[..] + [2]; // proof helper
  var res2 := RemoveElements(a2, a3);
  assert res2 == [2, 3] ;
}
