// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  requires a != null && b != null
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..] && res[i] !in b[..] && res[i] !in res[..i]
  ensures |res| <= a.Length
  ensures forall i :: 0 <= i < a.Length ==> (a[i] in b[..] || a[i] in res[..] || a[i] in a[..i])
  ensures res == seqc(a[..], x => x !in b[..] && x !in res[..], id)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < |res| ==> res[j] in a[..i] && res[j] !in b[..] && res[j] !in res[..j]
    invariant forall j :: 0 <= j < i ==> a[j] in b[..] || a[j] in res[..] || a[j] in a[..j]
    invariant |res| <= i
    invariant res == seqc(a[..i], x => x !in b[..] && x !in res[..], id)
  {
    if a[i] !in b[..] && a[i] !in res[..] {
      res := res + [a[i]];
    }
  }
}

// Auxiliary sequence comprehension function
ghost function seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
{
  if s == [] then []
  else if f(s[|s|-1]) then seqc(s[..|s|-1], f, g) + [g(s[|s|-1])]
  else seqc(s[..|s|-1], f, g)
}

// Identity function
function id<T>(x: T): T
{
  x
}

// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  assert a1[..] == [1, 2, 3, 4]; // helper
  assert a2[..] == [2, 4]; // helper
  assert res1 == [1, 3];
}

// Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  assert a1[..] == [1, 2, 3, 4]; // helper
  assert res2 == [];
  var res3 := RemoveElements(a1, a2);
  assert a2[..] == []; // helper
  assert res3 == [1, 2, 3, 4];
}


// Duplicates in the first array
method RemoveElementsDups(){
  var a1 := new int[] [1, 2, 1, 3];
  var a2 := new int[] [1, 2, 1, 3, 2];
  var a3 := new int[] [1];
  var res1 := RemoveElements(a1, a3);
  assert a1[..] == [1, 2, 1, 3]; // helper
  assert a3[..] == [1]; // helper
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert a2[..] == [1, 2, 1, 3, 2]; // helper
  assert res2 == [2, 3] ;
}
