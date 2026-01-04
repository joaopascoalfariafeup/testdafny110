// Auxiliary predicates (also help quantifier triggering)
ghost predicate MatchAt<T(==)>(s: seq<T>, t: seq<T>, i: int)
{
  0 <= i && i + |s| <= |t| && s == t[i..i+|s|]
}

ghost predicate NoMatchAt<T(==)>(s: seq<T>, t: seq<T>, i: int)
{
  0 <= i && i + |s| <= |t| && s != t[i..i+|s|]
}

// Interesting example that previously had a bug for empty lists.
// Checks if a sequence 's' is contained (as a subsequence) in another sequence 't'.
method IsSublist<T(==)>(s: seq<T>, t: seq<T>) returns (result: bool)
    ensures result <==> (exists i:int {:trigger MatchAt(s,t,i)} :: MatchAt(s,t,i))
{
    var n := |t| - |s|;
    if n >= 0 {
        for i := 0 to n + 1
            invariant 0 <= i <= n + 1
            invariant forall j:int {:trigger NoMatchAt(s,t,j)} :: 0 <= j < i ==> NoMatchAt(s,t,j)
        {
            // for-loop range guarantees i <= n here; make it explicit for slicing
            assert i <= n;
            assert 0 <= i;
            assert i + |s| <= n + |s|;
            assert n + |s| == |t|;
            assert i + |s| <= |t|;

            if s == t[i.. i+|s|] {
                assert MatchAt(s, t, i);
                assert exists k:int {:trigger MatchAt(s,t,k)} :: MatchAt(s,t,k);
                return true;
            }
            // establish the next element for the invariant maintenance
            assert NoMatchAt(s, t, i);
        }

        // From the loop invariant (j < n+1) to the desired "all valid j" statement
        assert forall j:int {:trigger t[j..j+|s|]} ::
            0 <= j && j + |s| <= |t| ==> s != t[j.. j+|s|] by
        {
            intro j;
            if 0 <= j && j + |s| <= |t| {
                assert j <= |t| - |s|;
                assert j <= n;
                assert j < n + 1;
                assert NoMatchAt(s, t, j);
            }
        };

        assert !(exists k:int {:trigger MatchAt(s,t,k)} :: MatchAt(s,t,k));
    } else {
        assert |t| < |s|;
        assert forall j:int {:trigger t[j..j+|s|]} ::
            0 <= j && j + |s| <= |t| ==> s != t[j.. j+|s|];
        assert !(exists k:int {:trigger MatchAt(s,t,k)} :: MatchAt(s,t,k));
    }
    return false;
}


// Test cases checked statically.
method IsSublistTest(){
    var a0: seq<int> := [1, 0, 2, 2];
    var a1: seq<int> := [1, 2];
    var a2: seq<int> :=  [0, 2, 2];
    var a3: seq<int> := [];

    var r1 := IsSublist(a1, a0);
    assert !r1; 

    var r2 := IsSublist(a2, a0);
    assert r2; 

    var r3 := IsSublist(a3, a0);
    assert r3;

    var r4 := IsSublist(a3, a3);
    assert r4;
}
