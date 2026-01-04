
ghost function filter<T>(s: seq<T>, p: T -> bool): seq<T>
  requires forall i :: 0 <= i < |s| ==> p(s[i]) ==> exists j :: 0 <= j < |s| && s[j] == s[i]
{
  if |s| == 0 then [] 
  else if p(s[0]) then [s[0]] + filter(s[1..], p) 
  else filter(s[1..], p)
}

method MoveZeroesToEnd(a: array<int>) returns (nz: nat)
    modifies a
    requires a != null
    ensures forall i :: 0 <= i < nz ==> old(a[i]) != 0 && a[i] != 0
    ensures forall i :: nz <= i < a.Length ==> a[i] == 0
    ensures nz == |filter(a[..], x => x != 0)|
    ensures multiset(filter(a[..], x => x != 0)) == multiset(filter(old(a[..]), x => x != 0))
{
    nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant 0 <= nz <= i <= a.Length
        invariant nz == |filter(a[..i], x => x != 0)|
        invariant forall j :: 0 <= j < nz ==> old(a[j]) != 0 && a[j] != 0
        invariant forall j :: nz <= j < i ==> a[j] == 0
        invariant multiset(filter(a[..i], x => x != 0)) == multiset(filter(old(a[..i]), x => x != 0))
    {
        if a[i] != 0 {
            if nz < i {
                var temp := a[nz];
                a[nz] := a[i];
                a[i] := temp; // swap non-zero element to the left
            }
            nz := nz + 1; // increment number of non-zero elements
        }
    }    
}

method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 0, 3];
    var nz1 := MoveZeroesToEnd(a1);
    assert nz1 == 2;
    assert a1[..] == [1, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1];
    var nz2 := MoveZeroesToEnd(a2);
    assert nz2 == 2;
    assert a2[..] == [1, 1, 0, 0];
}

