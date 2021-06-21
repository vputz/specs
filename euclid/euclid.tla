------------------------------- MODULE euclid -------------------------------
\* blatantly cribbing from https://github.com/belaban/pluscal/blob/master/euclid.tla
EXTENDS Naturals, TLC

CONSTANTS M, N

\* whether or not i divides into j an integer number of times
Divides(i,j) == \E k \in 0..j : j = i*k

\* whether or not i divides into j and k and is the greatest common divisor
\* Curious about this condition actually.  See the WP article: 'Thus any number c
\* which divides both a and b must also divide g
IsGCD(i,j,k) == /\ Divides(i,j)
	       /\ Divides(i,k)
	       /\ \A r \in 0..j \cup 0..k : Divides(r,i) /\ Divides(r,j) => Divides(r,i)

(* --algorithm euclid

variables
  m \in 1..M, n \in 1..N,
  x = m, y = n;

begin
  while x /= y do
    if x < y then
      y := y-x;
    else
      x := x-y;
    end if;
  end while;
  assert IsGCD(x, m, n);
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "5865bc8d" /\ chksum(tla) = "eab1351")
VARIABLES m, n, x, y, pc

vars == << m, n, x, y, pc >>

Init == (* Global variables *)
        /\ m \in 1..M
        /\ n \in 1..N
        /\ x = m
        /\ y = n
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x /= y
               THEN /\ IF x < y
                          THEN /\ y' = y-x
                               /\ x' = x
                          ELSE /\ x' = x-y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(IsGCD(x, m, n), 
                              "Failure of assertion at line 31, column 3.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ UNCHANGED << m, n >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
l\* Modification History
\* Created Mon Jun 14 11:02:14 CDT 2021 by vputz
