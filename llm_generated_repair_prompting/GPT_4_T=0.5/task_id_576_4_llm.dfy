
ghost predicate IsSubsequence<T(==)>(s: seq<T>, t: seq<T>, i: nat)
{
    0 <= i <= |t| - |s| && s == t[i..i + |s|]
}

ghost predicate ExistsSubsequence<T(==)>(s: seq<T>, t: seq<T>, i: nat)
{
    exists j :: 0 <= j < i && IsSubsequence(s, t, j)
}

method IsSublist<T(==)>(s: seq<T>, t: seq<T>) returns (result: bool)
  ensures result <==> (exists i :: IsSubsequence(s, t, i))
{
    var n := |t| - |s|;
    result := false;
    if n >= 0 {
        for i := 0 to n + 1
          invariant 0 <= i <= n + 1
          invariant ExistsSubsequence(s, t, i) <==> (result && |s| > 0)
        {
            if s == t[i.. i+|s|] {
                result := true;
                return;
            }
        }
    }
}

// Test cases checked statically.
method IsSublistTest(){
    var a0: seq<int> := [1, 0, 2, 2];
    var a1: seq<int> := [1, 2];
    var a2: seq<int> :=  [0, 2, 2];
    var a3: seq<int> := [];

    var r1 := IsSublist(a1, a0);
    assert a1 in a0 ==> r1;
    assert !r1; 

    var r2 := IsSublist(a2, a0);
    assert a2 in a0 ==> r2;
    assert r2; 

    var r3 := IsSublist(a3, a0);
    assert a3 in a0 ==> r3;
    assert r3;

    var r4 := IsSublist(a3, a3);
    assert a3 in a3 ==> r4;
    assert r4;
}

