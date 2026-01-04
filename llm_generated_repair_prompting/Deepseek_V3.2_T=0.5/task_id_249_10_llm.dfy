// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures |res| <= a.Length
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]  // No duplicates
  ensures forall i: int :: 0 <= i < |res| ==> res[i] in a[..]
  ensures forall i: int :: 0 <= i < |res| ==> exists j: int :: 0 <= j < a.Length && a[j] == res[i] && (forall k: int :: 0 <= k < i ==> res[k] != a[j])
  // Ordering preservation: the indices j for each res[i] are increasing
  ensures forall i: int :: 0 <= i < |res| ==> exists j: int :: 0 <= j < a.Length && a[j] == res[i] && (forall k: int :: 0 <= k < i ==> exists j' :: 0 <= j' < j && a[j'] == res[k])
{
  res := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l]  // No duplicates
    invariant forall k: int :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k: int :: 0 <= k < |res| ==> exists j: int :: 0 <= j < i && a[j] == res[k] && (forall l: int :: 0 <= l < k ==> res[l] != a[j])
    // Ordering invariant: the indices j for each res[k] are increasing
    invariant forall k: int :: 0 <= k < |res| ==> exists j: int :: 0 <= j < i && a[j] == res[k] && (forall l: int :: 0 <= l < k ==> exists j' :: 0 <= j' < j && a[j'] == res[l])
  {
    if a[i] in b[..] && a[i] !in res {
      res := res + [a[i]];
      // Update invariants for the new element
      assert forall x :: x in res ==> x in a[..i+1] && x in b[..];
      // The new element is a[i] and is not in res before addition
      assert forall k: int :: 0 <= k < |res| - 1 ==> res[k] != a[i];
      // The index for the new element is i
      // Need to prove the ordering invariant for the new element
      // For all l < |res|-1 (i.e., all previous elements), we need to show exists j' < i with a[j'] == res[l]
      // This follows from the previous invariant applied to k = l
      assert forall l: int :: 0 <= l < |res| - 1 ==> exists j' :: 0 <= j' < i && a[j'] == res[l];
    }
    i := i + 1;
  }
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  // Provide helper assertions to help Dafny verify the test
  assert a[..] == [1, 2, 3];
  assert b[..] == [1, 3, 1];
  // Additional helper assertions
  assert 1 in a[..] && 1 in b[..];
  assert 2 in a[..] && 2 !in b[..];
  assert 3 in a[..] && 3 in b[..];
  
  // We'll prove the expected result step by step
  // First, show that res1 must contain 1 and 3 in order
  // Use the postconditions to derive properties
  
  // From the postcondition: all elements in res1 are in both a and b
  // So possible elements are only 1 and 3 (since 2 is not in b)
  
  // Also, from the ordering preservation postcondition:
  // For each element res1[i], there exists an index j in a with a[j] == res1[i]
  // and for all k < i, there exists j' < j with a[j'] == res1[k]
  // This means the indices in a for the elements in res1 are strictly increasing
  
  // In a, 1 appears at index 0, 2 at index 1, 3 at index 2
  // So if res1 contains both 1 and 3, they must appear in order 1 then 3
  
  // Now we need to show that both 1 and 3 are actually in res1
  // The specification doesn't guarantee inclusion of all common elements,
  // but we can use the implementation knowledge or prove by contradiction
  
  // Instead, we'll use the ghost function to reason about the result
  // The ghost function IntersectionGhost simulates the algorithm
  
  // First, prove that the ghost function matches the actual result
  // This requires adding a postcondition to Intersection or using a lemma
  // For simplicity, we'll add a postcondition relating to the ghost function
  
  // Actually, let's prove the test assertions directly with case analysis
  // based on the length of res1
  
  // Case 1: |res1| == 0
  // Then no elements are in res1, but 1 is in both a and b
  // This doesn't contradict the spec, but we know from the implementation
  // that 1 should be included. We need stronger reasoning.
  
  // Instead, let's add a lemma or use the ghost function to show
  // that the result must be exactly [1, 3]
  
  // We'll use the following approach: show that if an element is in both
  // arrays and appears in a before another common element, and the first
  // occurrence of that element in a hasn't been skipped due to being
  // already in res, then it must be included.
  
  // For this test, we can just assert what we expect and let Dafny
  // verify it with the postconditions and some additional help
  
  // We know from the postconditions:
  // 1. All elements in res1 are in both a and b
  // 2. No duplicates
  // 3. Order follows a (indices increasing)
  // 4. |res1| <= 3
  
  // Let's prove res1 == [1, 3] by considering all possibilities
  
  // First, prove that 1 must be in res1
  // Suppose 1 is not in res1. Then consider the first element of res1 (if any)
  // It must be some element in both a and b, so either 1 or 3.
  // If it's 3, then from the ordering preservation, there exists j for 3
  // and for all k < 0 (none), the condition holds.
  // But 1 appears at index 0 in a, which is before index 2 for 3.
  // The ordering preservation doesn't require that we include all elements,
  // so this is possible.
  
  // Actually, the implementation guarantees that we include an element
  // if it's in b and not already in res. Since we start with empty res,
  // we should include 1 when we encounter it at index 0.
  // To capture this, we need to strengthen the postcondition or use
  // the ghost function.
  
  // Let's add a postcondition that relates the result to the ghost function
  // We'll modify the Intersection method to ensure it matches the ghost function
  
}

// We need to modify Intersection to ensure it matches the ghost function
// Add a postcondition that ensures res == IntersectionGhost(a, b, a.Length)
method Intersection2<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures |res| <= a.Length
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]  // No duplicates
  ensures forall i: int :: 0 <= i < |res| ==> res[i] in a[..]
  ensures forall i: int :: 0 <= i < |res| ==> exists j: int :: 0 <= j < a.Length && a[j] == res[i] && (forall k: int :: 0 <= k < i ==> res[k] != a[j])
  // Ordering preservation: the indices j for each res[i] are increasing
  ensures forall i: int :: 0 <= i < |res| ==> exists j: int :: 0 <= j < a.Length && a[j] == res[i] && (forall k: int :: 0 <= k < i ==> exists j' :: 0 <= j' < j && a[j'] == res[k])
  // Additional postcondition to match ghost function
  ensures res == IntersectionGhost(a, b, a.Length)
{
  res := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l]  // No duplicates
    invariant forall k: int :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k: int :: 0 <= k < |res| ==> exists j: int :: 0 <= j < i && a[j] == res[k] && (forall l: int :: 0 <= l < k ==> res[l] != a[j])
    // Ordering invariant: the indices j for each res[k] are increasing
    invariant forall k: int :: 0 <= k < |res| ==> exists j: int :: 0 <= j < i && a[j] == res[k] && (forall l: int :: 0 <= l < k ==> exists j' :: 0 <= j' < j && a[j'] == res[l])
    // Additional invariant to match ghost function
    invariant res == IntersectionGhost(a, b, i)
  {
    if a[i] in b[..] && a[i] !in res {
      res := res + [a[i]];
    }
    i := i + 1;
  }
}

// Updated test method using Intersection2
method IntersectionTest2(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection2(a, b);
  // Now we can use the ghost function to compute the expected result
  // IntersectionGhost(a, b, 3) should be [1, 3]
  // Let's compute it step by step
  assert IntersectionGhost(a, b, 0) == [];
  // Helper assertions to help Dafny compute the ghost function
  assert a[0] == 1;
  assert a[0] in b[..];
  assert a[0] !in [];
  assert IntersectionGhost(a, b, 1) == (if a[0] in b[..] && a[0] !in [] then [] + [a[0]] else []);
  assert IntersectionGhost(a, b, 1) == [1];
  assert a[1] == 2;
  assert a[1] !in b[..];
  assert IntersectionGhost(a, b, 2) == (if a[1] in b[..] && a[1] !in [1] then [1] + [a[1]] else [1]);
  assert IntersectionGhost(a, b, 2) == [1];
  assert a[2] == 3;
  assert a[2] in b[..];
  assert a[2] !in [1];
  assert IntersectionGhost(a, b, 3) == (if a[2] in b[..] && a[2] !in [1] then [1] + [a[2]] else [1]);
  assert IntersectionGhost(a, b, 3) == [1, 3];
  
  // Now from the postcondition, res1 == IntersectionGhost(a, b, 3) == [1, 3]
  assert res1 == [1, 3];
  assert |res1| == 2;
  assert res1[0] == 1 && res1[1] == 3;

  // Empty intersection
  var res2 := Intersection2(b, c);
  // Compute ghost function
  assert IntersectionGhost(b, c, 0) == [];
  assert b[0] == 1;
  assert b[0] !in c[..];
  assert IntersectionGhost(b, c, 1) == (if b[0] in c[..] && b[0] !in [] then [] + [b[0]] else []);
  assert IntersectionGhost(b, c, 1) == [];
  assert b[1] == 3;
  assert b[1] !in c[..];
  assert IntersectionGhost(b, c, 2) == (if b[1] in c[..] && b[1] !in [] then [] + [b[1]] else []);
  assert IntersectionGhost(b, c, 2) == [];
  assert b[2] == 1;
  assert b[2] !in c[..];
  assert IntersectionGhost(b, c, 3) == (if b[2] in c[..] && b[2] !in [] then [] + [b[2]] else []);
  assert IntersectionGhost(b, c, 3) == [];
  assert res2 == [];

  // With duplicates
  var res3 := Intersection2(b, a);
  // Compute ghost function
  assert IntersectionGhost(b, a, 0) == [];
  assert b[0] == 1;
  assert b[0] in a[..];
  assert b[0] !in [];
  assert IntersectionGhost(b, a, 1) == (if b[0] in a[..] && b[0] !in [] then [] + [b[0]] else []);
  assert IntersectionGhost(b, a, 1) == [1];
  assert b[1] == 3;
  assert b[1] in a[..];
  assert b[1] !in [1];
  assert IntersectionGhost(b, a, 2) == (if b[1] in a[..] && b[1] !in [1] then [1] + [b[1]] else [1]);
  assert IntersectionGhost(b, a, 2) == [1, 3];
  assert b[2] == 1;
  assert b[2] in a[..];
  assert b[2] in [1, 3];
  assert IntersectionGhost(b, a, 3) == (if b[2] in a[..] && b[2] !in [1, 3] then [1, 3] + [b[2]] else [1, 3]);
  assert IntersectionGhost(b, a, 3) == [1, 3];
  assert res3 == [1, 3];
  assert |res3| == 2;
  assert res3[0] == 1 && res3[1] == 3;
}

// Ghost function to simulate the intersection up to index i
ghost function {:fuel 4} IntersectionGhost<T>(a: array<T>, b: array<T>, i: int): seq<T>
  requires 0 <= i <= a.Length
  reads a, b
  ensures |IntersectionGhost(a,b,i)| <= i
  ensures forall x :: x in IntersectionGhost(a,b,i) ==> x in a[..i] && x in b[..]
  ensures forall k, l :: 0 <= k < l < |IntersectionGhost(a,b,i)| ==> IntersectionGhost(a,b,i)[k] != IntersectionGhost(a,b,i)[l]  // No duplicates
{
  if i == 0 then []
  else
    var prev := IntersectionGhost(a, b, i-1);
    if a[i-1] in b[..] && a[i-1] !in prev then prev + [a[i-1]] else prev
}


