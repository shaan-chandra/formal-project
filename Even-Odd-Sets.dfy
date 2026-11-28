
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
{
  if n % 2 == 0 {
    ModuloEven(n);
  }
  else {
    ModuloOdd(n);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{
  if isEven(n) {
    var m :| n == 2 * m;
    assert invertParity(n) == 2 * m + 1;
  }

  if isOdd(n) {
    var m :| n == 2 * m + 1;
    assert invertParity(n) == 2 * (m + 1);
  }
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
  forall x :: x in s ==> isEven(x)
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
  forall x :: x in s ==> isOdd(x)
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
requires isSet(s)
// Every element of s times n is in t
ensures forall x :: x in s ==> x * n in t
// Every element of t is an element of s times n
ensures forall y :: y in t ==> exists x :: x in s && y == x * n
ensures isSet(t)
// if n == 0 then t={0}
ensures n == 0 && |s| > 0 ==> t == [0]
// Multiplying by n != 0 is injective
ensures n != 0 ==> |t| == |s|
ensures isEven(n) ==> isEvenSet(t)
ensures isEvenSet(s) ==> isEvenSet(t)
ensures isOdd(n) && isOddSet(s) ==> isOddSet(t)
{
  t := [];
  var i := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant forall x :: x in s[..i] ==> x * n in t
    invariant forall y :: y in t ==> exists x :: x in s[..i] && y == x * n
  {
    t := addToSet(t, s[i] * n);
    i := i + 1;
  }
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
requires isSet(s1) && isSet(s2)
// Every product x*y s.t. x in s1 and y in s2 is in t
ensures forall x, y :: x in s1 && y in s2 ==> x * y in t
// Every element of t is a product x*y
ensures forall z :: z in t ==> exists x, y :: x in s1 && y in s2 && z == x * y
ensures isSet(t)
// At most one element per pair
ensures |t| <= |s1| * |s2|
ensures |s1| == 0 || |s2| == 0 ==> |t| == 0
ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := [];
  var i := 0;

  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
  {
    var j := 0;

    while j < |s2|
      invariant 0 <= j <= |s2|
      invariant isSet(t)
    {
      t := addToSet(t, s1[i] * s2[j]);
      j := j + 1;
    }
    i := i + 1;
  }
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
requires isSet(s)
// Every element of s inverted is in t
ensures forall x :: x in s ==> invertParity(x) in t
// Every element of t is an inverted element of s
ensures forall y :: y in t ==> exists x :: x in s && y == invertParity(x)
ensures isSet(t)
// x + 1 is injective
ensures |t| == |s|
ensures isEvenSet(s) ==> isOddSet(t)
ensures isOddSet(s) ==> isEvenSet(t)
{
  t := [];
  var i := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant forall x :: x in s[..i] ==> invertParity(x) in t
    invariant forall y :: y in t ==> exists x :: x in s[..i] && y == invertParity(x)
  {
    t := addToSet(t, invertParity(s[i]));
    i := i + 1;
  }
}
