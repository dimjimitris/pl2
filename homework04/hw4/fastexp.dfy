/* Στοιχεία Σπουδαστή
Όνομα:
ΑΜ:

Συμπληρώστε το Dafny version που χρησιμοποιήσατε.
Dafny version: 
*/

function pow(b: nat, e: nat) : nat
decreases e
{ 
    if e == 0 then 1 else b * pow(b, e - 1)
}


method FastExponentiation(a: nat, n: nat) returns (res: nat)
// ensures that the result is correct with respect to the functional specification [pow]
ensures res == pow(a, n) 
{
  // fill in here
  return 42;
}