// Interesting example that previously had a bug for empty lists.
// Checks if a sequence 's' is contained (as a subsequence) in another sequence 't'.
predicate {:opaque} Sublist<T>(s: seq<T>, t: seq<T>)
{
  exists i :: 0 <= i && i + |s| <= |t| && s == t[i..i+|s|]
}

lemma {:opaque} LemmaNoSublistWhenLonger<T>(s: seq<T>, t: seq<T>)
  ensures |s| > |t| ==> !Sublist(s, t)
{
}

method IsSublist<T(==)>(s: seq<T>, t: seq<T>) returns (result: bool)
  ensures result <==> Sublist(s, t)
{
    var n := |t| - |s|;
    if n >= 0 {
        for i := 0 to n + 1
          invariant 0 <= i <= n + 1
          invariant forall j :: 0 <= j < i ==> s != t[j..j+|s|]
        {
            if s == t[i.. i+|s|] {
                return true;
            }
        }
        assert forall j :: 0 <= j <= n ==> s != t[j..j+|s|];
        assert !Sublist(s, t);
    } else {
        LemmaNoSublistWhenLonger(s, t);
        assert !Sublist(s, t);
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
