/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

ghost function {:fuel 20} RecSeq(n: nat): seq<nat>
  ensures |RecSeq(n)| == n + 1
  ensures RecSeq(n)[0] == 0
{
  if n == 0 then
    [0]
  else
    var prev := RecSeq(n - 1);
    var cand: int := prev[n - 1] - n;
    if cand > 0 && (forall j: nat :: j < |prev| ==> prev[j] != cand) then
      prev + [cand as nat]
    else
      prev + [prev[n - 1] + n]
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires len <= a.Length
  ensures res <==> (exists j: nat :: j < len && a[j] == x)
{
  for i := 0 to len
    invariant 0 <= i <= len
    invariant forall j: nat :: j < i ==> a[j] != x
  {
    if a[i] == x {
      return true;
    }
  }
  return false;
}

// Returns the n-th term of Recaman's sequence
method Recaman(n: nat) returns (res: nat)
  ensures res == RecSeq(n)[n]
{
  var a: array<nat> := new nat[n+1];
  a[0] := 0;
  for i := 1 to n + 1
    invariant 1 <= i <= n + 1
    invariant a.Length == n + 1
    invariant a[..i] == RecSeq((i - 1) as nat)
  {
    var x := a[i-1] - i;
    if x > 0 {
      var c := Contains(x, a, i);
      if !c {
        a[i] := x;
      } 
      else {
        a[i] := a[i-1] + i;
      }
    } 
    else {
      a[i] := a[i-1] + i;
    }

    // help Dafny relate the array update to the sequence spec
    assert a[..i+1] == a[..i] + [a[i]];

    // prove the next-step spec for the loop invariant
    var prev := RecSeq((i - 1) as nat);
    assert a[..i] == prev;

    var cand: int := prev[(i - 1) as nat] - i;
    if cand > 0 && (forall j: nat :: j < |prev| ==> prev[j] != cand) {
      // this corresponds to the branch x>0 && !Contains(x,a,i)
      assert x == cand;
      assert !c;
      assert forall j: nat :: j < i ==> a[j] != x; // from !c and Contains postcondition
      assert forall j: nat :: j < |prev| ==> prev[j] != cand; // since prev == a[..i]
      assert a[i] == cand as nat;
      assert a[..i+1] == prev + [cand as nat];
    } else {
      // otherwise we add previous + i
      assert a[i] == prev[(i - 1) as nat] + i;
      assert a[..i+1] == prev + [prev[(i - 1) as nat] + i];
    }

    assert a[..i+1] == RecSeq(i as nat);
  }
  assert a[..n+1] == RecSeq(n);
  return a[n];
}

method TestRecaman() {
  var r0 := Recaman(0); assert r0 == 0;
  var r1 := Recaman(1); assert r1 == 1;
  var r2 := Recaman(2); assert r2 == 3;  
  var r3 := Recaman(3); assert r3 == 6;
  var r4 := Recaman(4); assert r4 == 2;
  var r5 := Recaman(5); assert r5 == 7;
  var r6 := Recaman(6); assert r6 == 13;
  var r7 := Recaman(7); assert r7 == 20;
  var r8 := Recaman(8); assert r8 == 12; // decreases
}
