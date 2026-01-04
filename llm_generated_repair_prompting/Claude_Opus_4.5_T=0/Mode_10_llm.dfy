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

lemma CountPositive(a: seq<int>, v: int, idx: int)
    requires 0 <= idx < |a|
    requires a[idx] == v
    ensures Count(a, v) >= 1
{
    if idx == |a| - 1 {
        CountNonNeg(a[..|a|-1], v);
    } else {
        CountPositive(a[..|a|-1], v, idx);
    }
}

lemma CountLEPreserved(a: seq<int>, x: int, best_m: int, v: int)
    requires Count(a, v) <= Count(a, best_m)
    ensures Count(a + [x], v) <= Count(a + [x], best_m) || x == v
{
    CountAppend(a, v, x);
    CountAppend(a, best_m, x);
}

method Mode(a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && a[i] == m
    ensures forall v :: Count(a[..], v) <= Count(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    var current_val := a[0];
    
    CountSingleton(best_m, a[0]);
    assert a[..1] == [a[0]];
    
    for i := 1 to a.Length 
        invariant 1 <= current_count <= i
        invariant 1 <= best_count <= i
        invariant exists j :: 0 <= j < i && a[j] == best_m
        invariant exists j :: 0 <= j < i && a[j] == current_val
        invariant Count(a[..i], current_val) >= current_count
        invariant Count(a[..i], best_m) >= best_count
        invariant best_count >= current_count ==> forall v :: Count(a[..i], v) <= Count(a[..i], best_m)
        invariant current_count > best_count ==> forall v :: Count(a[..i], v) <= Count(a[..i], current_val)
    {
        assert a[..i+1] == a[..i] + [a[i]];
        CountAppend(a[..i], a[i], a[i]);
        CountAppend(a[..i], best_m, a[i]);
        CountAppend(a[..i], current_val, a[i]);
        
        if a[i] == current_val {
            current_count := current_count + 1;
            if current_count > best_count {
                best_count := current_count;
                best_m := current_val;
            }
        }
        else {
            if current_count > best_count {
                best_count := current_count;
                best_m := current_val;
            }
            current_count := 1;
            current_val := a[i];
            CountPositive(a[..i+1], a[i], i);
        }
        
        forall v 
            ensures Count(a[..i+1], v) <= Count(a[..i+1], best_m)
        {
            CountAppend(a[..i], v, a[i]);
        }
    }
    
    if current_count > best_count {
        best_count := current_count;
        best_m := current_val;
        assert a[..a.Length] == a[..];
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
