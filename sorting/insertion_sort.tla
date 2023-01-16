--------------------------- MODULE insertion_sort ---------------------------
EXTENDS Sequences, Naturals, TLC, Sorting

CONSTANTS

MaxValue

(* --algorithm InsertionSort
variables
  Max \in 1 .. MaxValue,
  input \in PermutationKey(Max),
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4e45112ece253fee4f639d582685f436 (chksum(pcal) = "d85c5101" /\ chksum(tla) = "8c90068e") (chksum(pcal) = "a318bb87" /\ chksum(tla) = "4ec27d6c") (chksum(pcal) = "b5ee45a6" /\ chksum(tla) = "58b16345") (chksum(pcal) = "b5ee45a6" /\ chksum(tla) = "e46f7016")
VARIABLES Max, input, index, output, pc

vars == << Max, input, index, output, pc >>

Init == (* Global variables *)
        /\ Max \in 1 .. MaxValue
        /\ input \in PermutationKey(Max)
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
                             "Failure of assertion at line 25, column 2.")
                   /\ Assert(IsSorted(output), 
                             "Failure of assertion at line 26, column 2.")
                   /\ pc' = "Done"
                   /\ UNCHANGED << index, output >>
        /\ UNCHANGED << Max, input >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == sort
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e0ae8fc1cacce77a5e08699eebcb4182

=============================================================================
\* Modification History
\* Last modified Wed Jan 04 16:48:33 GMT 2023 by vputz
\* Created Tue Oct 20 11:03:18 CDT 2020 by vputz
