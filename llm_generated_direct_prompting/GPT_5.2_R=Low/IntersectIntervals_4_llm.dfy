// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).
predicate EmptyInterval(i: (real, real))
{
  i.0 >= i.1
}

predicate NonEmptyInterval(i: (real, real))
{
  i.0 < i.1
}

// Computes the intersection of two intervals
function intersect(i: (real, real), j :(real, real)): (real, real)  {
    (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

function IntersectUpTo(s: seq<(real, real)>, n: int): (real, real)
  requires 1 <= n <= |s|
  decreases n
{
  if n == 1 then s[0] else intersect(IntersectUpTo(s, n-1), s[n-1])
}

lemma EmptyPersistsLeft(x: (real, real), y: (real, real))
  requires EmptyInterval(x)
  ensures EmptyInterval(intersect(x, y))
{
  var z := intersect(x, y);
  assert z.0 >= x.0;
  assert z.1 <= x.1;
  assert z.0 >= z.1;
}

lemma EmptyPrefixImpliesEmptyAll(s: seq<(real, real)>, n: int)
  requires 1 <= n <= |s|
  requires EmptyInterval(IntersectUpTo(s, n))
  ensures EmptyInterval(IntersectUpTo(s, |s|))
  decreases |s| - n
{
  if n == |s| {
  } else {
    EmptyPersistsLeft(IntersectUpTo(s, n), s[n]);
    assert intersect(IntersectUpTo(s, n), s[n]) == IntersectUpTo(s, n + 1);
    EmptyPrefixImpliesEmptyAll(s, n + 1);
  }
}

method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> NonEmptyInterval(a[k])
  ensures r == (0.0, 0.0) ==> EmptyInterval(IntersectUpTo(a[..], a.Length))
  ensures r != (0.0, 0.0) ==> r == IntersectUpTo(a[..], a.Length) && NonEmptyInterval(r)
{
    r := a[0];
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant r == IntersectUpTo(a[..], i)
      invariant NonEmptyInterval(r)
    {
        r := intersect(r, a[i]);
        if r.0 >= r.1 {
            EmptyPrefixImpliesEmptyAll(a[..], i + 1);
            return (0.0, 0.0);
        }
    }
}



method TestIntersectIntervals()
{
    // Overlaping intervals
    var a1 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    var r1 := IntersectIntervals(a1);
    assert r1 == (2.0, 3.0);

    // Disjoint intervals
    var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    var r2 := IntersectIntervals(a2);
    assert r2 == (0.0, 0.0);
}
