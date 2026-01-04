// Small helper: from a concrete witness index, derive an existential occurrence
lemma ExistsFromWitness<T>(a: array?<T>, x: T, w: int)
  requires a != null
  requires 0 <= w < a.Length
  requires a[w] == x
  ensures exists k :: 0 <= k < a.Length && a[k] == x
{
  assert exists k :: 0 <= k < a.Length && a[k] == x by {
    // witness k := w
    assert 0 <= w < a.Length && a[w] == x;
  }
}

// Searches for a value 'x' in an array 'a' and returns an index
// where x occurs, or -1 if not found.
method LinearSearch<T(==)>(a: array?<T>, x: T) returns (index: int)
  requires a != null
  modifies {}
  ensures index == -1 || 0 <= index < a.Length
  ensures 0 <= index < a.Length ==> a[index] == x
  // If found, it is the *first* occurrence
  ensures 0 <= index < a.Length ==> (forall k :: 0 <= k < index ==> a[k] != x)
  // Found iff there exists an occurrence (existential form is often easier to use in clients)
  ensures (exists k :: 0 <= k < a.Length && a[k] == x) ==> index != -1
  ensures index != -1 ==> (exists k :: 0 <= k < a.Length && a[k] == x)
  ensures index == -1 <==> (forall k :: 0 <= k < a.Length ==> a[k] != x)
  // Minimality phrased directly: any occurrence is at/after the returned index
  ensures 0 <= index < a.Length ==> (forall k :: 0 <= k < a.Length && a[k] == x ==> index <= k)
{
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != x
  {
    if a[i] == x {
      // Prove the strengthened postcondition about minimality
      assert forall k :: 0 <= k < a.Length && a[k] == x ==> i <= k;
      return i;
    }
  }
  return -1;
}

method TestLinearSearch() {
  var a := new int[] [3, 2, 1, 3];
  assert a[..] == [3, 2, 1, 3];
  // Help the verifier use concrete element facts
  assert a[0] == 3 && a[1] == 2 && a[2] == 1 && a[3] == 3;

  // Existence facts (proved via an explicit witness) to help clients use the method's existential postcondition
  ExistsFromWitness(a, 2, 1);
  assert exists k :: 0 <= k < a.Length && a[k] == 2;

  var i := LinearSearch(a, 2);

  // Use the method's postcondition implication together with the existential we proved
  assert (exists k :: 0 <= k < a.Length && a[k] == 2) ==> i != -1;
  assert exists k :: 0 <= k < a.Length && a[k] == 2;
  assert i != -1;

  // Help the verifier conclude i == 1 from the postconditions
  assert 0 <= i < a.Length;
  assert a[i] == 2;
  assert 0 <= 1 < a.Length && a[1] == 2;
  // minimality: returned index is <= any occurrence
  assert i <= 1;

  // rule out i == 0 using concrete array contents
  assert a[0] == 3;
  assert 3 != 2;
  if i == 0 {
    assert a[0] == 2; // from a[i] == 2 and i == 0
  }
  assert i != 0;
  // with 0 <= i and i <= 1, the only possibility left is 1
  assert i == 1;

  assert forall k :: 0 <= k < a.Length ==> a[k] != 0;
  var j := LinearSearch(a, 0);
  assert j == -1;

  // Prove the existential for 3 using an explicit witness
  ExistsFromWitness(a, 3, 0);
  assert exists k :: 0 <= k < a.Length && a[k] == 3;

  var k := LinearSearch(a, 3);

  // Use the method's postcondition implication together with the existential we proved
  assert (exists t :: 0 <= t < a.Length && a[t] == 3) ==> k != -1;
  assert exists t :: 0 <= t < a.Length && a[t] == 3;
  assert k != -1;

  // Help the verifier conclude k == 0 from minimality and the known occurrence at 0
  assert 0 <= k < a.Length;
  assert a[k] == 3;
  assert (forall t :: 0 <= t < a.Length && a[t] == 3 ==> k <= t);
  // instantiate minimality at t = 0
  assert 0 <= 0 < a.Length && a[0] == 3;
  assert k <= 0;
  assert 0 <= k;
  assert k == 0;

  assert k == 0 || k == 3;
}
