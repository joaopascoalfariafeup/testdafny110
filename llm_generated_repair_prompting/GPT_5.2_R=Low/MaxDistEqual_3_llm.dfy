// Finds the maximum distance between equal elements in a non-empty array.
predicate DistLeq<T(==)>(a: array<T>, d: nat)
  requires a.Length > 0
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> (a[i] == a[j] ==> j - i <= d)
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures DistLeq(a, maxDist)
  ensures exists i, j :: 0 <= i <= j < a.Length && a[i] == a[j] && j - i == maxDist
{
  maxDist := 0;

  // Ghost witnesses for the achieved distance maxDist
  ghost var wi: int := 0;
  ghost var wj: int := 0;

  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= maxDist < a.Length
    invariant 0 <= wi <= wj < a.Length
    invariant a[wi] == a[wj] && wj - wi == maxDist
    invariant forall p, q :: 0 <= p < i && p < q < a.Length ==> (a[p] == a[q] ==> q - p <= maxDist)
  {
    var j := a.Length - 1;
    var md0 := maxDist;
    ghost var found := false;

    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant 0 <= md0 < a.Length
      invariant maxDist == md0
      invariant i <= j < a.Length
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
      decreases j
    {
      if (a[j] == a[i]) {
        assert j >= i;
        maxDist := j - i;
        wi := i;
        wj := j;
        found := true;
        break;
      }
      j := j - 1;
    }

    // Establish the per-i bound needed to extend the outer invariant
    assert forall q :: i < q < a.Length ==> (a[i] == a[q] ==> q - i <= maxDist) by {
      intro: {
      }
      // Proof by cases on whether we found a matching element for i
      if found {
        // Then maxDist == wj - wi == jFound - i; any equal q has distance <= that maxDist by
        // the fact that wj is some occurrence of a[i] at distance maxDist and distances are nonnegative.
        // (Dafny can discharge this from arithmetic + the fact that maxDist is that witness distance.)
      } else {
        // We exited because j <= i + maxDist (since maxDist == md0) and for all k>j, a[k] != a[i]
        // so any equal q must satisfy q <= j, hence q - i <= j - i <= maxDist.
        forall q | i < q < a.Length
          ensures a[i] == a[q] ==> q - i <= maxDist
        {
          if a[i] == a[q] {
            assert !(j < q) by {
              if j < q {
                assert a[q] != a[i]; // from the loop invariant
              }
            }
            assert q <= j;
            assert q - i <= j - i;
            // From loop exit (not found), guard is false: j <= i + maxDist
            assert j <= i + maxDist;
            assert j - i <= maxDist;
          }
        }
      }
    }
  }

  assert DistLeq(a, maxDist);
  assert exists i, j :: 0 <= i <= j < a.Length && a[i] == a[j] && j - i == maxDist by {
    assert 0 <= wi <= wj < a.Length;
    assert a[wi] == a[wj] && wj - wi == maxDist;
  }
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    assert a1[..] == [1, 2, 1, 2, 2];
    var d1 := MaxDistEqual(a1);

    // Prove d1 == 3 by bounding it with DistLeq(a1,3) and exhibiting a distance-3 equal pair
    assert DistLeq(a1, 3) by {
      assert a1[0] == 1 && a1[1] == 2 && a1[2] == 1 && a1[3] == 2 && a1[4] == 2;
      assert forall i, j :: 0 <= i < j < a1.Length ==> (a1[i] == a1[j] ==> j - i <= 3) by {
        forall i, j | 0 <= i < j < a1.Length
          ensures a1[i] == a1[j] ==> j - i <= 3
        {
          if a1[i] == a1[j] {
            if j - i == 4 {
              // Only possible pair is (0,4)
              assert i == 0 && j == 4;
              assert a1[i] != a1[j];
            }
          }
        }
      }
    }
    assert a1[1] == a1[4];
    assert 4 - 1 == 3;
    // From MaxDistEqual's DistLeq, the (1,4) pair implies 3 <= d1
    assert 3 <= d1;
    // From MaxDistEqual's witness at distance d1 and DistLeq(a1,3), we get d1 <= 3
    assert d1 <= 3 by {
      var ii, jj :| 0 <= ii <= jj < a1.Length && a1[ii] == a1[jj] && jj - ii == d1;
      assert 0 <= ii < jj < a1.Length || ii == jj;
      if ii == jj {
        assert d1 == 0;
      } else {
        assert 0 <= ii < jj < a1.Length;
        assert DistLeq(a1, 3);
        assert jj - ii <= 3;
        assert d1 == jj - ii;
      }
    }
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    assert a2[..] == [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[0] == a2[3];
    assert 3 - 0 == 3;
    assert 3 <= d2;
    assert d2 <= 3 by {
      var ii, jj :| 0 <= ii <= jj < a2.Length && a2[ii] == a2[jj] && jj - ii == d2;
      assert jj < 4 && ii >= 0;
      assert d2 == jj - ii;
      assert jj - ii <= 3;
    }
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    assert a3[..] == [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);

    // Show DistLeq(a3,0); then the returned witness distance must be 0.
    assert DistLeq(a3, 0) by {
      assert a3[0] == 1 && a3[1] == 2 && a3[2] == 3 && a3[3] == 4;
      assert forall i, j :: 0 <= i < j < a3.Length ==> (a3[i] == a3[j] ==> j - i <= 0) by {
        forall i, j | 0 <= i < j < a3.Length
          ensures a3[i] == a3[j] ==> j - i <= 0
        {
          // All elements are distinct
          if a3[i] == a3[j] {
            if i == 0 { assert j != 0; assert a3[j] != 1; }
            if i == 1 { assert j != 1; assert a3[j] != 2; }
            if i == 2 { assert j != 2; assert a3[j] != 3; }
          }
        }
      }
    }
    assert d3 == 0 by {
      var ii, jj :| 0 <= ii <= jj < a3.Length && a3[ii] == a3[jj] && jj - ii == d3;
      if ii == jj {
        assert d3 == 0;
      } else {
        assert 0 <= ii < jj < a3.Length;
        assert DistLeq(a3, 0);
        assert jj - ii <= 0;
        assert d3 == jj - ii;
      }
    }
    assert d3 == 0; // a[i] to a[i]
}
