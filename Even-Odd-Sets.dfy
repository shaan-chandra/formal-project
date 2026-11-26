
/*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
// The next three lemmas prove that modulo-based definition is equivalent to existential-based definition
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m; // Hint for Dafny to choose n/2 as witness for the existential in the isEven predicate
	}
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
// Useful lemma that may be used later
// It shows that the product of two integers is even if at least one of them is even
lemma EvenTimesAny(n1: int, n2: int)
  ensures isEven(n1) || isEven(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) {
	  var m1 := n1 / 2;
	  assert n1 * n2 == 2 * (m1 * n2);
  } else if isEven(n2) {
	  var m2 := n2 / 2;
	  assert n1 * n2 == 2 * (n1 * m2);
  }
}

/*** Odd ***/

ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{
}

lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{
  if n % 2 != 0 {
    // if not even
    var k := n / 2;
    assert n == (2 * k) + 1;
  }
}

lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{
  if checkOdd(n) {
    ModuloOdd(n);
    assert isOdd(n);
  }
  if isOdd(n) {
    OddModulo(n);
    assert checkOdd(n);
  }
}

lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{
  if isOdd(n1) && isOdd(n2) {
    checkOddCorrect(n1 * n2);
    assert n1 * n2 % 2 != 0;
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ // TODO: complete this proof
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO: complete this proof
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
 forall i: int, j:int :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s)
{ // TODO: complete this method
  b := true; 
  var res: set<int> := {}; 
  var i := 0;
  while i < |s| {
    var x := s[i];
    if x in res {
      b := false;
    }
    res := res + {x}; 
    i := i + 1; 
  }
}

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
 // TODO: complete this predicate
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{ // TODO: complete this method
  var i := 0;
  b := true; 
  while i < |s| {
    if !checkEven(s[i]) {
      b := false;
    }
    i := i + 1;
  }
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  // TODO: complete this predicate
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{ // TODO: complete this method
  var i := 0;
  b := true; 
  while i < |s| {
    if !checkOdd(s[i]) {
      b := false;
    }
    i := i + 1;
  }
}

/*** Set Operations ***/

// For the following methods specify their behaviour so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
// Marks will be awarded for specifying as much as possible all relevant properties of the output.

/* Adds n to a set s, making sure it remains a set */
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
// Specify the behavior of this method so that your specification characterizes the allowed outputs,
  // Marks will be awarded for specifying as much as possible all relevant properties of the output.
  // Hint: You don't need to reimplement addToSet as a function to use in your specification.
  ensures forall i :: i in b <==> (i in s || i == n)
  ensures n in s ==> |b| == |s|
  ensures n !in s ==> |b| == |s| + 1
  ensures isSet(s) ==> isSet(b)
{
  if n in s {
    b := s;
  }
  else {
    b := s + [n];
  }
  return b;
}


/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
ensures forall i :: i in t <==> (i in s1 || i in s2)
ensures isSet(s1) ==> isSet(t)
ensures |t| <= |s1| + |s2|
ensures isSet(s1) ==> |t| >= |s1|
{ // TODO: Implement the method
  var i := 0;
  t := s1;
  while i < |s2| 
  invariant 0 <= i <= |s2|
  invariant forall x :: x in t <==> (x in s1 || x in s2[..i])
  invariant isSet(s1) ==> isSet(t)
  invariant |s1| <= |t| <= |s1| + i
  {
    t := addToSet(t, s2[i]);
    i := i + 1;
  }
}

/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
ensures forall i :: i in t <==> (i in s1 && i in s2)
ensures isSet(t)
ensures |t| <= |s1|
{ // TODO: Implement the method
  
  var i := 0;
  t := [];
  while i < |s1|
  invariant 0 <= i <= |s1|
  invariant forall x :: x in t <==> (x in s1[..i] && x in s2)
  invariant isSet(t)
  invariant |t| <= i
  {
    if s1[i] in s2 {
      t := addToSet(t, s1[i]);
    }
    i := i + 1;
  }
  return t;
}

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
ensures isSet(t)
ensures forall i :: (i in s1 && i !in s2) <==> i in t
ensures |t| <= |s1|
{ // TODO: Implement the method
  t := [];
  var i := 0;
  while i < |s1| 
  invariant 0 <= i <= |s1|
  invariant isSet(t)
  invariant forall j :: (j in s1[..i] && j !in s2) <==> j in t
  invariant |t| <= i
  {
    if s1[i] !in s2 {
      t := addToSet(t, s1[i]);
    }
    i := i + 1;
  }
  return t;
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}
