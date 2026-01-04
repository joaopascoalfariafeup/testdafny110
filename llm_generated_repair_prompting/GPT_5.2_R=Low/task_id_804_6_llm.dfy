// Checks if a number is even.
predicate IsEven(n: int) {
  n % 2 == 0
}

// Checks if an array contains an even number.
method ContainsEvenNumber(a: array<int>) returns (result: bool)
  modifies {}
  // Keep the intended spec, but also split it into implications to help the prover at call sites
  ensures result <==> (exists k :: 0 <= k < a.Length && IsEven(a[k]))
  ensures result ==> (exists k :: 0 <= k < a.Length && IsEven(a[k]))
  ensures !result ==> (forall k :: 0 <= k < a.Length ==> !IsEven(a[k]))
{
  result := false;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    // If result is true, there is some even element in the array
    invariant result ==> (exists k :: 0 <= k < a.Length && IsEven(a[k]))
    // If result is false, all checked positions so far are odd
    invariant !result ==> (forall k :: 0 <= k < i ==> !IsEven(a[k]))
    // If an even has been seen in the checked prefix, then result must be true
    invariant (exists k :: 0 <= k < i && IsEven(a[k])) ==> result
  {
    if IsEven(a[i]) {
      // Help the verifier establish the existential for the invariant/postcondition
      assert 0 <= i < a.Length;
      assert (exists k :: 0 <= k < a.Length && IsEven(a[k]));
      result := true;
      break;
    }
  }
}

method ContainsEvenNumberTest(){
  var a1 := new int[] [1, 2, 3];
  assert a1[..] == [1, 2, 3];
  assert 0 <= 1 < a1.Length;
  assert IsEven(a1[1]); // helper for the existential in ContainsEvenNumber's postcondition
  assert (exists k :: 0 <= k < a1.Length && IsEven(a1[k]));
  var out1 := ContainsEvenNumber(a1);
  // Help instantiate/consume the callee postcondition with this concrete array
  assert out1 <==> (exists k :: 0 <= k < a1.Length && IsEven(a1[k]));
  assert out1;

  var a2:= new int[] [1, 2, 1, 4];
  assert a2[..] == [1, 2, 1, 4];
  assert 0 <= 1 < a2.Length;
  assert IsEven(a2[1]);
  assert (exists k :: 0 <= k < a2.Length && IsEven(a2[k]));
  var out2 := ContainsEvenNumber(a2);
  // Help instantiate/consume the callee postcondition with this concrete array
  assert out2 <==> (exists k :: 0 <= k < a2.Length && IsEven(a2[k]));
  assert out2;

  var a3:= new int[] [1,1];
  assert a3[..] == [1, 1];
  assert forall k :: 0 <= k < a3.Length ==> !IsEven(a3[k]);
  var out3 := ContainsEvenNumber(a3);
  // Help instantiate/consume the callee postcondition with this concrete array
  assert out3 <==> (exists k :: 0 <= k < a3.Length && IsEven(a3[k]));
  assert ! out3;
}
