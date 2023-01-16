---- MODULE Sorting ----
EXTENDS Sequences, TLC, Naturals

IsSorted(S) == \A x \in 1..Len(S):
	      \A y \in 1 .. x:
	      S[y] <= S[x]

\* from learntla.com/tla/sets
Range(T) == { T[x]: x \in DOMAIN T }

\* from learntla.com/tla/functions
PermutationKey(n) == { key \in [1..n -> 1..n]: Range(key) = 1..n }

IndexLTE(seq, n) ==
  LET indexesLTE == {x \in 1..Len(seq) : seq[x] <= n}
  IN IF indexesLTE = {}
     THEN 0
     ELSE CHOOSE x \in indexesLTE: \A y \in {y \in indexesLTE: y /= x}: y < x

Left(seq, n) ==
  LET rightIndex == IndexLTE(seq, n) IN
  IF rightIndex = 0
  THEN << >>
  ELSE SubSeq(seq, 1, rightIndex)

Right(seq, n) ==
  LET rightIndex == IndexLTE(seq, n) IN
  IF rightIndex = Len(seq)
  THEN << >>
  ELSE SubSeq(seq, rightIndex + 1, Len(seq))

====
