/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

ghost predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function method InversionCount(s: seq<T>): nat
{
  |set p: (int,int) | 0 <= p.0 < p.1 < |s| && s[p.0] > s[p.1]|
}

lemma SwapDecreasesInversions(s: seq<T>, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] > s[j]
  ensures InversionCount(s[i := s[j]][j := s[i]]) < InversionCount(s)
{
  var s2 := s[i := s[j]][j := s[i]];
  var A := set p: (int,int) | 0 <= p.0 < p.1 < |s| && s[p.0] > s[p.1];
  var B := set p: (int,int) | 0 <= p.0 < p.1 < |s2| && s2[p.0] > s2[p.1];

  assert (i,j) in A;
  assert s2[i] == s[j];
  assert s2[j] == s[i];
  assert s2[i] <= s2[j];
  assert (i,j) !in B;

  assert forall p: (int,int) :: p in B ==> p in A
  {
    intro p;
    var x := p.0;
    var y := p.1;
    assert 0 <= x < y < |s|;
    if x != i && x != j && y != i && y != j {
      assert s2[x] == s[x];
      assert s2[y] == s[y];
      assert s[x] > s[y];
    } else if x == i && y == j {
      assert false;
    } else if x == i && y != j {
      assert y != i;
      assert s2[i] == s[j];
      assert s2[y] == s[y];
      if y < i {
        assert false;
      } else if i < y && y < j {
        // s2[i] > s2[y] means s[j] > s[y]; since i<y<j, then (y,j) was an inversion in s
        assert s[j] > s[y];
        assert s[y] > s[i];
        assert s[y] > s[j];
      } else {
        assert j < y;
        assert s[j] > s[y];
        assert s[i] > s[y];
      }
    } else if x == j && y != i {
      assert y != j;
      assert s2[j] == s[i];
      assert s2[y] == s[y];
      if y < j {
        if y == i {
          assert false;
        } else if y < i {
          assert s[y] > s[i];
        } else {
          assert i < y < j;
          assert s[y] > s[i];
        }
      } else {
        assert false;
      }
    } else if y == i {
      assert x < i;
      assert x != j;
      assert s2[x] == s[x];
      assert s2[i] == s[j];
      assert s[x] > s[j];
      assert s[x] > s[i];
    } else if y == j {
      assert x < j;
      if x == i {
        assert false;
      } else if x < i {
        assert s2[x] == s[x];
        assert s2[j] == s[i];
        assert s[x] > s[i];
      } else {
        assert i < x < j;
        assert s2[x] == s[x];
        assert s2[j] == s[i];
        assert s[x] > s[i];
      }
  }

  assert B <= A;
  assert B != A;
  assert |B| < |A|;
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   decreases InversionCount(a[..])
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var s := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      ghost var s2 := a[..];
      SwapDecreasesInversions(s, i, j);
      RawSort(a); // proceed recursivelly
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
