// Helper predicate to avoid triggerless quantifiers and to simplify specs
ghost predicate InPrefix(a: array<int>, n: int, v: int)
  reads a
{
  exists j :: 0 <= j < n && a[j] == v
}

// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i :: 0 < i < a.Length ==> a[i-1] <= a[i]
  ensures InPrefix(a, a.Length, m)
  ensures forall v :: InPrefix(a, a.Length, v) ==>
            (var cm := |set j | 0 <= j < a.Length && a[j] == m|;
             var cv := |set j | 0 <= j < a.Length && a[j] == v|;
             cm >= cv)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= best_count
      invariant 1 <= current_count
      invariant InPrefix(a, i, best_m)
      invariant best_count <= i
      invariant current_count <= i
      // The current run is the suffix of equal elements ending at i-1
      invariant (forall j :: 0 <= j < i ==> a[j] == a[i-1] ==> i - current_count <= j)
      invariant current_count == |set j | 0 <= j < i && a[j] == a[i-1] && i - current_count <= j|
      invariant forall v :: InPrefix(a, i, v) ==>
                (var cb := |set j | 0 <= j < i && a[j] == best_m|;
                 var cv := |set j | 0 <= j < i && a[j] == v|;
                 cb >= cv)
    {
        if a[i] == a[i-1] {
            current_count := current_count + 1;
            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            }
        }
        else {
            current_count := 1;
        }
    }
    return best_m;
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    assert a[..] == [1,1,2,2,3];
    var m := Mode(a);
    // Help the verifier connect the postcondition to this concrete test
    assert InPrefix(a, a.Length, 1);
    assert InPrefix(a, a.Length, 2);
    assert InPrefix(a, a.Length, 3);

    var c1 := |set j | 0 <= j < a.Length && a[j] == 1|;
    var c2 := |set j | 0 <= j < a.Length && a[j] == 2|;
    var c3 := |set j | 0 <= j < a.Length && a[j] == 3|;
    assert c1 == 2;
    assert c2 == 2;
    assert c3 == 1;

    if m == 3 {
      // From mode postcondition with v=1, count(m) >= count(1), but 1 occurs more than 3
      assert (var cm := |set j | 0 <= j < a.Length && a[j] == m|;
              var cv := |set j | 0 <= j < a.Length && a[j] == 1|;
              cm >= cv);
      assert |set j | 0 <= j < a.Length && a[j] == 3| >= |set j | 0 <= j < a.Length && a[j] == 1|;
      assert false;
    }

    // Now m must be 1 or 2
    assert m == 1 || m == 2;
}
