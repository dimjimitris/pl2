/* Στοιχεία Σπουδαστή
Όνομα: ΔΗΜΗΤΡΙΟΣ ΓΕΩΡΓΟΥΣΗΣ
ΑΜ: 03119005

Συμπληρώστε το Dafny version που χρησιμοποιήσατε.
Dafny version: 3.10.0
*/

function pow(b: nat, e: nat) : nat
decreases e
{ 
    if e == 0 then 1 else b * pow(b, e - 1)
}

lemma pow_lemma(x: nat, n: nat)
  ensures (
    pow(x, n) == pow(x * x, n / 2) * pow(x, n % 2)
  )
{
  if n == 0 {

  } else {
    pow_lemma(x, n - 1); // use the IH
  }
}

method FastExponentiation(a: nat, n: nat) returns (res: nat)
// ensures that the result is correct with respect to the functional specification [pow]
ensures res == pow(a, n) 
{
  var base := a;
  var exp := n;

  res := 1;
  while exp > 0
  invariant res * pow(base, exp) == pow(a, n)
  {
    pow_lemma(base, exp);

    if exp % 2 == 1 {
      res := res * base;
    }

    base := base * base;
    exp := exp / 2;
  }
}
