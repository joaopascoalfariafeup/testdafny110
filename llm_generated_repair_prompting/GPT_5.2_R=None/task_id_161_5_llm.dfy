// Ghost function that defines the intended result sequence:
// all elements of a (in order) that are not in b and are first occurrences in a.
ghost function SeqRemove<T>(sa: seq<T>, sb: seq<T>): seq<T>
  ensures forall x :: x in SeqRemove(sa, sb) ==> x in sa && x !in sb
  ensures forall i,j :: 0 <= i < j < |SeqRemove(sa, sb)| ==> SeqRemove(sa, sb)[i] != SeqRemove(sa, sb)[j]
  // Only talks about elements that are actually "first occurrences" in sa
  // (avoids the need to reason about later duplicates on the return path)
  ensures forall i :: 0 <= i < |sa| && sa[i] !in sa[..i] ==>
            ((sa[i] !in sb) <==> sa[i] in SeqRemove(sa, sb))
  decreases |sa|
{
  if |sa| == 0 then []
  else
    var t := SeqRemove(sa[..|sa|-1], sb);
    if sa[|sa|-1] !in sb && sa[|sa|-1] !in sa[..|sa|-1] then t + [sa[|sa|-1]] else t
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

