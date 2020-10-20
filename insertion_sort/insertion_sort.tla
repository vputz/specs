--------------------------- MODULE insertion_sort ---------------------------
EXTENDS Sequences, Naturals, TLC

CONSTANTS

MaxValue

IsSorted(S) == \A x \in 1..Len(S):
	      \A y \in 1 .. x:
	      y <= x

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

(* --algorithm InsertionSort
variables
  input \in PermutationKey(MaxValue),
  index = 1,
  output = << >>;
  \* helper variables

 begin  \* algorithm implementation
 sort:
   while index <= Len(input) do
     output := Left(output, input[index])
                \o << input[index] >>
		\o Right(output, input[index]);
     index := index + 1;
   end while;
 print(output);
 assert Len(output) = Len(input);
 assert IsSorted(output)
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4e45112ece253fee4f639d582685f436
VARIABLES input, index, output, pc

vars == << input, index, output, pc >>

Init == (* Global variables *)
        /\ input \in PermutationKey(MaxValue)
        /\ index = 1
        /\ output = << >>
        /\ pc = "sort"

sort == /\ pc = "sort"
        /\ IF index <= Len(input)
              THEN /\ output' = Left(output, input[index])
                                 \o << input[index] >>
                                 \o Right(output, input[index])
                   /\ index' = index + 1
                   /\ pc' = "sort"
              ELSE /\ PrintT((output))
                   /\ Assert(Len(output) = Len(input), 
                             "Failure of assertion at line 52, column 2.")
                   /\ Assert(IsSorted(output), 
                             "Failure of assertion at line 53, column 2.")
                   /\ pc' = "Done"
                   /\ UNCHANGED << index, output >>
        /\ input' = input

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == sort
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e0ae8fc1cacce77a5e08699eebcb4182

=============================================================================
\* Modification History
\* Last modified Tue Oct 20 11:12:16 CDT 2020 by vputz
\* Created Tue Oct 20 11:03:18 CDT 2020 by vputz
