// Auxiliary, order-preserving comprehension used to define SeqRemove in a way
// that is easy for the verifier to unfold along the same direction as the loop.
ghost function {:fuel 3} SeqC<T>(s: seq<T>, f: T -> bool): seq<T>
  decreases |s|
{
  if |s| == 0 then []
  else
    var t := SeqC(s[..|s|-1], f);
    if f(s[|s|-1]) then t + [s[|s|-1]] else t
}

ghost predicate FirstOk<T>(sa: seq<T>, sb: seq<T>, i: int)
{
  0 <= i < |sa| &&
  sa[i] !in sb &&
  sa[i] !in sa[..i]
}

// Ghost function that defines the intended result sequence:
// all elements of a (in order) that are not in b and are first occurrences in a.
ghost function {:fuel 3} SeqRemove<T>(sa: seq<T>, sb: seq<T>): seq<T>
  ensures forall x :: x in SeqRemove(sa, sb) ==> x in sa && x !in sb
  ensures forall i,j :: 0 <= i < j < |SeqRemove(sa, sb)| ==> SeqRemove(sa, sb)[i] != SeqRemove(sa, sb)[j]
  ensures forall i :: 0 <= i < |sa| && sa[i] !in sa[..i] ==>
            ((sa[i] !in sb) <==> sa[i] in SeqRemove(sa, sb))
  ensures SeqRemove(sa, sb) == SeqC(sa, (x: T) => x !in sb && x !in sa[..IndexOf(sa, x)])
  decreases |sa|
{
  // Keep the original algorithmic intent/definition, but also tie it to SeqC via a cheap equality lemma below.
  if |sa| == 0 then []
  else
    var t := SeqRemove(sa[..|sa|-1], sb);
    if sa[|sa|-1] !in sb && sa[|sa|-1] !in sa[..|sa|-1] then t + [sa[|sa|-1]] else t
}

// IndexOf for sequences, used only in the postcondition to connect to SeqC.
// (Total; returns the first index if present, otherwise 0. Only used under x in sa.)
ghost function {:fuel 3} IndexOf<T>(s: seq<T>, x: T): int
  ensures 0 <= IndexOf(s, x) < (if x in s then |s| else 1)
  ensures x in s ==> s[IndexOf(s, x)] == x
  ensures x in s ==> x !in s[..IndexOf(s, x)]
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == x then 0
  else 1 + IndexOf(s[1..], x)
}

lemma SeqRemoveStep<T>(sa: seq<T>, sb: seq<T>)
  requires |sa| > 0
  ensures SeqRemove(sa, sb) ==
            (var t := SeqRemove(sa[..|sa|-1], sb);
             if sa[|sa|-1] !in sb && sa[|sa|-1] !in sa[..|sa|-1] then t + [sa[|sa|-1]] else t)
{
}

// Returns a sequence with all elements belonging to the first array
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  requires a != null && b != null
  ensures res == SeqRemove(a[..], b[..])
  ensures forall x :: x in res ==> x in a[..] && x !in b[..]
  ensures forall i,j :: 0 <= i < j < |res| ==> res[i] != res[j]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == SeqRemove(a[..i], b[..])
    invariant forall x :: x in res ==> x in a[..i] && x !in b[..]
    invariant forall p,q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }

    // Help Dafny connect the loop step with SeqRemove's recursive definition
    assert a[..i+1] == a[..i] + [a[i]];
    SeqRemoveStep(a[..i+1], b[..]);
  }
}

// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  assert a1[..] == [1,2,3,4];
  assert a2[..] == [2,4];
  assert res1 == [1, 3];
}

// Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  assert a1[..] == [1,2,3,4];
  assert a2[..] == [];
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
  assert a1[..] == [1,2,1,3];
  assert a2[..] == [1,2,1,3,2];
  assert a3[..] == [1];
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert res2 == [2, 3] ;
}
