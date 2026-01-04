// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures |res| <= a.Length
  ensures forall k :: 0 <= k < |res| ==> res[k] < 0
  ensures forall k :: 0 <= k < a.Length && a[k] < 0 ==> a[k] in res
  ensures forall x :: x in res ==> x in a[..]
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] < 0 && a[j] < 0 ==> 
            exists idx_i, idx_j :: 0 <= idx_i < idx_j < |res| && res[idx_i] == a[i] && res[idx_j] == a[j]
  ensures |res| == countNegatives(a[..])
  ensures res == seqc(a[..], (x: int) => x < 0, (x: int) => x)
{
  res := [];
  var idx := 0;
  for i := 0 to a.Length
    invariant 0 <= idx <= i
    invariant |res| == idx
    invariant forall k :: 0 <= k < |res| ==> res[k] < 0
    invariant forall k :: 0 <= k < i && a[k] < 0 ==> a[k] in res
    invariant forall x :: x in res ==> x in a[..]
    invariant forall p, q :: 0 <= p < q < i && a[p] < 0 && a[q] < 0 ==> 
               exists idx_p, idx_q :: 0 <= idx_p < idx_q < |res| && res[idx_p] == a[p] && res[idx_q] == a[q]
    invariant idx == countNegatives(a[..i])
    invariant res == seqc(a[..i], (x: int) => x < 0, (x: int) => x)
  {
    if a[i] < 0 {
      res := res + [a[i]];
      idx := idx + 1;
      // Helper assertions to maintain invariants
      assert a[..i+1] == a[..i] + [a[i]];
      assert seqc(a[..i+1], (x: int) => x < 0, (x: int) => x) == 
             seqc(a[..i], (x: int) => x < 0, (x: int) => x) + (if a[i] < 0 then [a[i]] else []);
    } else {
      assert a[..i+1] == a[..i] + [a[i]];
      assert seqc(a[..i+1], (x: int) => x < 0, (x: int) => x) == 
             seqc(a[..i], (x: int) => x < 0, (x: int) => x);
    }
  }
}

// Helper function to count negatives in a sequence
function {:fuel 5} countNegatives(s: seq<int>): nat
{
  if |s| == 0 then 0
  else (if s[|s|-1] < 0 then 1 else 0) + countNegatives(s[..|s|-1])
}

// Helper function to extract negatives in order
ghost function {:fuel 5} seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
{
  if s == [] then []
  else if f(s[|s|-1]) then seqc(s[..|s|-1], f, g) + [g(s[|s|-1])]
  else seqc(s[..|s|-1], f, g)
}

// Test cases checked statically.
method FindNegativeNumbersTest(){
  var a1 := new int[] [-1, 4, 5, -6];
  var res1 := FindNegativeNumbers(a1);
  // Helper assertions to help Dafny verify the test
  assert a1[..] == [-1, 4, 5, -6];
  // Additional helper to prove the exact sequence
  assert a1[0] == -1 && a1[1] == 4 && a1[2] == 5 && a1[3] == -6;
  // Use the auxiliary function to compute expected result
  ghost var expected1 := seqc(a1[..], (x: int) => x < 0, (x: int) => x);
  // Prove expected1 using concrete computation
  calc {
    seqc([-1, 4, 5, -6], (x: int) => x < 0, (x: int) => x);
    seqc([-1, 4, 5], (x: int) => x < 0, (x: int) => x) + (if -6 < 0 then [-6] else []);
    seqc([-1, 4], (x: int) => x < 0, (x: int) => x) + (if 5 < 0 then [5] else []) + [-6];
    seqc([-1], (x: int) => x < 0, (x: int) => x) + (if 4 < 0 then [4] else []) + [] + [-6];
    seqc([], (x: int) => x < 0, (x: int) => x) + (if -1 < 0 then [-1] else []) + [] + [] + [-6];
    [] + [-1] + [] + [] + [-6];
    [-1, -6];
  }
  assert expected1 == [-1, -6];
  // The postconditions ensure res1 equals expected1
  assert res1 == [-1, -6];

  var a2:= new int[] [-1, -2, -3];
  var res2 := FindNegativeNumbers(a2);
  assert a2[..] == [-1, -2, -3];
  assert a2[0] == -1 && a2[1] == -2 && a2[2] == -3;
  ghost var expected2 := seqc(a2[..], (x: int) => x < 0, (x: int) => x);
  calc {
    seqc([-1, -2, -3], (x: int) => x < 0, (x: int) => x);
    seqc([-1, -2], (x: int) => x < 0, (x: int) => x) + [-3];
    seqc([-1], (x: int) => x < 0, (x: int) => x) + [-2] + [-3];
    seqc([], (x: int) => x < 0, (x: int) => x) + [-1] + [-2] + [-3];
    [] + [-1] + [-2] + [-3];
    [-1, -2, -3];
  }
  assert expected2 == [-1, -2, -3];
  assert res2 == [-1, -2, -3];

  var a3:= new int[] [0, 1];
  var res3 := FindNegativeNumbers(a3);
  assert a3[..] == [0, 1];
  assert a3[0] == 0 && a3[1] == 1;
  ghost var expected3 := seqc(a3[..], (x: int) => x < 0, (x: int) => x);
  calc {
    seqc([0, 1], (x: int) => x < 0, (x: int) => x);
    seqc([0], (x: int) => x < 0, (x: int) => x) + (if 1 < 0 then [1] else []);
    seqc([], (x: int) => x < 0, (x: int) => x) + (if 0 < 0 then [0] else []) + [];
    [] + [] + [];
    [];
  }
  assert expected3 == [];
  assert res3 == [];
}
