// Performs the bitwise XOR operation on two sequences of bv32 values (with equal length).
function XorSeq(a: seq<bv32>, b: seq<bv32>): seq<bv32>
  requires |a| == |b|
{
  seq i | 0 <= i < |a| :: a[i] ^ b[i]
}

method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures result == XorSeq(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant result == (seq j | 0 <= j < i :: a[j] ^ b[j])
  {
    result := result + [a[i] ^ b[i]];
  }
}

// Test cases checked statically.
method BitwiseXORTest(){
  // Typical case
  var res1 := BitwiseXOR([10, 4, 6, 9], [5, 2, 3, 3]);
  assert res1 == [15, 6, 5, 10];

  // Test with identical arguments
  var res2 := BitwiseXOR([11, 5, 7, 10], [11, 5, 7, 10]);
  assert res2 == [0, 0, 0, 0];
}

