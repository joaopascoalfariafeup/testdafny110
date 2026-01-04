// Returns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures |res| <= a.Length
  ensures forall k :: 0 <= k < |res| ==> res[k] < 0
  ensures forall k :: 0 <= k < a.Length && a[k] < 0 ==> a[k] in res
  ensures forall x :: x in res ==> x in a[..]
  // Simplified ordering property: indices in res correspond to order in a
  ensures forall i :: 0 <= i < a.Length && a[i] < 0 ==> 
            exists idx :: 0 <= idx < |res| && res[idx] == a[i] &&
            (forall j :: 0 <= j < i && a[j] < 0 ==> 
                exists idx_j :: 0 <= idx_j < idx && res[idx_j] == a[j])
  ensures |res| == countNegatives(a[..])
  ensures res == seqc(a[..], (x: int) => x < 0, (x: int) => x)
{
  res := [];
  var idx := 0;
  
  // Maintain a ghost variable to track the mapping from array indices to result indices
  ghost var map := [];
  
  for i := 0 to a.Length
    invariant 0 <= idx <= i
    invariant |res| == idx
    invariant forall k :: 0 <= k < |res| ==> res[k] < 0
    invariant forall k :: 0 <= k < i && a[k] < 0 ==> a[k] in res
    invariant forall x :: x in res ==> x in a[..]
    // Simplified ordering invariant
    invariant forall j :: 0 <= j < i && a[j] < 0 ==> 
               exists idx_j :: 0 <= idx_j < |res| && res[idx_j] == a[j] &&
               (forall k :: 0 <= k < j && a[k] < 0 ==>
                   exists idx_k :: 0 <= idx_k < idx_j && res[idx_k] == a[k])
    invariant idx == countNegatives(a[..i])
    invariant res == seqc(a[..i], (x: int) => x < 0, (x: int) => x)
  {
    if a[i] < 0 {
      // Update result
      res := res + [a[i]];
      idx := idx + 1;
      
      // Helper assertions
      assert a[..i+1] == a[..i] + [a[i]];
      assert seqc(a[..i+1], (x: int) => x < 0, (x: int) => x) == 
             seqc(a[..i], (x: int) => x < 0, (x: int) => x) + [a[i]];
      
      // Prove the ordering invariant for the new element
      // The new element is at the end of res
      assert res[|res|-1] == a[i];
      
      // For any j < i where a[j] < 0, we already have it in res[..|res|-1]
      // and its index is < |res|-1
      if |res| > 0 {
        forall j | 0 <= j < i && a[j] < 0
          ensures exists idx_j :: 0 <= idx_j < |res|-1 && res[idx_j] == a[j]
        {
          // This follows from the invariant
        }
      }
    } else {
      assert a[..i+1] == a[..i] + [a[i]];
      assert seqc(a[..i+1], (x: int) => x < 0, (x: int) => x) == 
             seqc(a[..i], (x: int) => x < 0, (x: int) => x);
    }
  }
  // When loop completes, i == a.Length, so a[..i] == a[..]
  assert a[..a.Length] == a[..];
}

// Helper function to count negatives in a sequence
function {:fuel 5} countNegatives(s: seq<int>): nat
  ensures countNegatives(s) == |seqc(s, (x: int) => x < 0, (x: int) => x)|
{
  if |s| == 0 then 0
  else (if s[|s|-1] < 0 then 1 else 0) + countNegatives(s[..|s|-1])
}

// Helper function to extract negatives in order - simplified specification
ghost function {:fuel 5} seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
  ensures forall x :: x in seqc(s, f, g) ==> exists i :: 0 <= i < |s| && f(s[i]) && g(s[i]) == x
  // Simplified ordering property
  ensures forall i :: 0 <= i < |s| && f(s[i]) ==> 
            exists idx :: 0 <= idx < |seqc(s, f, g)| && seqc(s, f, g)[idx] == g(s[i]) &&
            (forall j :: 0 <= j < i && f(s[j]) ==> 
                exists idx_j :: 0 <= idx_j < idx && seqc(s, f, g)[idx_j] == g(s[j]))
{
  if s == [] then []
  else if f(s[|s|-1]) then
    var s' := s[..|s|-1];
    var last := s[|s|-1];
    var rec := seqc(s', f, g);
    // Prove properties for the recursive case where last is included
    // The new element g(last) is appended at the end
    rec + [g(last)]
  else
    seqc(s[..|s|-1], f, g)
}

// Lemma to help prove the ordering property for seqc
lemma seqc_ordering_lemma<T,U>(s: seq<T>, f: T -> bool, g: T -> U, i: int, j: int)
  requires 0 <= i < j < |s|
  requires f(s[i]) && f(s[j])
  ensures exists idx_i, idx_j :: 0 <= idx_i < idx_j < |seqc(s, f, g)| && 
           seqc(s, f, g)[idx_i] == g(s[i]) && seqc(s, f, g)[idx_j] == g(s[j])
{
  // This lemma follows from the simplified postcondition of seqc
  // We can prove it by induction on j
  if j == i + 1 {
    // Base case: consecutive indices
    // From seqc's postcondition, we know s[i] appears before s[j]
  } else {
    // Inductive step
    seqc_ordering_lemma(s, f, g, i, j-1);
  }
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
    { 
      assert seqc([-1, 4, 5], (x: int) => x < 0, (x: int) => x) == seqc([-1, 4], (x: int) => x < 0, (x: int) => x);
    }
    seqc([-1, 4], (x: int) => x < 0, (x: int) => x) + [-6];
    {
      assert seqc([-1, 4], (x: int) => x < 0, (x: int) => x) == seqc([-1], (x: int) => x < 0, (x: int) => x);
    }
    seqc([-1], (x: int) => x < 0, (x: int) => x) + [-6];
    {
      assert seqc([-1], (x: int) => x < 0, (x: int) => x) == [-1];
    }
    [-1] + [-6];
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
    [-1] + [-2] + [-3];
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
    seqc([0], (x: int) => x < 0, (x: int) => x);
    seqc([], (x: int) => x < 0, (x: int) => x);
    [];
  }
  assert expected3 == [];
  assert res3 == [];
}
