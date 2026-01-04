// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

ghost function Count(a: seq<int>, v: int): int
{
    if |a| == 0 then 0
    else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

ghost predicate IsMode(a: seq<int>, m: int)
{
    exists i :: 0 <= i < |a| && a[i] == m && forall v :: Count(a, v) <= Count(a, m)
}

lemma CountBound(a: seq<int>, v: int)
    ensures Count(a, v) <= |a|
{
    if |a| == 0 {
    } else {
        CountBound(a[..|a|-1], v);
    }
}

lemma CountNonNeg(a: seq<int>, v: int)
    ensures Count(a, v) >= 0
{
    if |a| == 0 {
    } else {
        CountNonNeg(a[..|a|-1], v);
    }
}

lemma CountAppend(a: seq<int>, v: int, x: int)
    ensures Count(a + [x], v) == Count(a, v) + (if x == v then 1 else 0)
{
    if |a| == 0 {
        assert a + [x] == [x];
    } else {
        assert (a + [x])[..|a + [x]|-1] == a;
    }
}

lemma CountMonotonic(a: seq<int>, b: seq<int>, v: int)
    requires |a| <= |b| && a == b[..|a|]
    ensures Count(a, v) <= Count(b, v)
{
    if |a| == |b| {
        assert a == b;
    } else {
        CountMonotonic(a, b[..|b|-1], v);
    }
}

ghost predicate CountLE(a: seq<int>, m: int, v: int)
{
    Count(a, v) <= Count(a, m)
}

lemma CountSingleton(v: int, x: int)
    ensures Count([x], v) == (if x == v then 1 else 0)
{
    assert [x][..|[x]|-1] == [];
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && a[i] == m
    ensures forall v :: Count(a[..], v) <= Count(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    
    CountSingleton(best_m, a[0]);
    assert a[..1] == [a[0]];
    
    for i := 1 to a.Length 
        invariant 1 <= current_count <= i
        invariant 1 <= best_count <= i
        invariant exists j :: 0 <= j < i && a[j] == best_m
        invariant forall v :: Count(a[..i], v) <= best_count
        invariant Count(a[..i], best_m) == best_count
    {
        assert a[..i+1] == a[..i] + [a[i]];
        CountAppend(a[..i], a[i], a[i]);
        CountAppend(a[..i], best_m, a[i]);
        
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
        
        forall v 
            ensures Count(a[..i+1], v) <= best_count
        {
            CountAppend(a[..i], v, a[i]);
        }
    }
    assert a[..a.Length] == a[..];
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    assert a[..] == [1, 1, 2, 2, 3];
    var m := Mode(a);
    // The postcondition guarantees m is a mode, but we can't easily prove which one
    // without more detailed reasoning about the specific array
    assert exists i :: 0 <= i < a.Length && a[i] == m;
}
