// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).

predicate FirstOccurrence<T(==)>(a: seq<T>, i: int)
{
  0 <= i < |a| &&
  (forall j :: 0 <= j < i ==> a[j] != a[i])
}

function BuildRemoved<T(==)>(a: seq<T>, b: seq<T>, n: nat): seq<T>
  decreases n
{
  if n == 0 then
    []
  else
    var r := BuildRemoved(a, b, n - 1);
    if a[n - 1] !in b && FirstOccurrence(a, n - 1) then r + [a[n - 1]] else r
}

lemma BuildRemovedStep<T(==)>(a: seq<T>, b: seq<T>, i: nat)
  requires i < |a|
  ensures BuildRemoved(a, b, i + 1) ==
            (if a[i] !in b && FirstOccurrence(a, i) then BuildRemoved(a, b, i) + [a[i]] else BuildRemoved(a, b, i))
{
}

method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == BuildRemoved(a[..], b[..], a.Length)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == BuildRemoved(a[..], b[..], i)
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
    BuildRemovedStep(a[..], b[..], i);
    assert res == BuildRemoved(a[..], b[..], i + 1);
  }
}




// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
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
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert res2 == [2, 3] ;
}

