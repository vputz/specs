---- MODULE euclid_native ----
EXTENDS Naturals, TLC

CONSTANTS M, N

\* Whether i divides into J evenly and thus is a divisor
Divides(i,j) == \E x \in 0..j : x*i = j

\* Whether i divides into j and k evenly and is a GCD of j and k
IsGCD(i,j,k) ==
  LET xs == 0..j \cup 0..k IN
    /\ Divides(i,j)
    /\ Divides(i,k)
    /\ ~ \E x \in xs :
      /\ x > i
      /\ Divides(x,j)
      /\ Divides(x,k)

VARIABLES m, n, x, y \*, pc

vars == << m, n, x, y >> \*, pc >>

Init == \* global variables
  /\ m \in 1..M
  /\ n \in 1..N
  /\ x = m
  /\ y = n
\*  /\ pc = "Init"

XLess ==
  /\ x < y
  /\ y' = y - x
  /\ UNCHANGED << m, n, x >> \*, pc >>

YLess ==
  /\ y < x
  /\ x' = x - y
  /\ UNCHANGED << m, n, y >> \*, pc >>

Terminating ==
  /\ x = y
  /\ IsGCD(x,m,n)
  /\ PrintT(<< x,m,n >>)
\*  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ XLess
  \/ YLess
  \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars

\* Termination ==
\*  <> Terminating \*(pc = "Done")

====
