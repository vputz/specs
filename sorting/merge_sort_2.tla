---- MODULE merge_sort_2 ----

EXTENDS Sequences, Naturals, TLC, Sorting

CONSTANTS

MaxValue

RECURSIVE Merge(_, _)
RECURSIVE MergeSort(_)

Max(lhs, rhs) ==
  IF (lhs > rhs) THEN lhs ELSE rhs

Min(lhs, rhs) ==
  IF (lhs < rhs) THEN lhs ELSE rhs

Merge(lhs, rhs) ==
   IF Len(lhs) = 0 /\ Len(rhs) = 0 THEN << >>
   ELSE IF Len(lhs) = 0 /\ Len(rhs) > 0 THEN rhs
   ELSE IF Len(rhs) = 0 /\ Len(lhs) > 0 THEN lhs
   ELSE
     LET
       l1 == Head(lhs)
       r1 == Head(rhs)
     IN
       IF (l1 < r1) THEN << l1 >> \o Merge(Tail(lhs), rhs)
       ELSE << r1 >> \o Merge(lhs, Tail(rhs))
     

MergeSort(s) ==
  IF Len(s) <= 1 THEN s ELSE
  LET
    halfway == Len(s) \div 2
    lhs == SubSeq(s, 1, halfway)
    rhs == SubSeq(s, halfway+1, Len(s))
  IN
    Merge(MergeSort(lhs), MergeSort(rhs))


(* --algorithm MergeSort

(* In this version, we'll use sequences a bit more like one would expect *)

variables
  ThisMax \in 1..MaxValue,
  input \in PermutationKey(ThisMax),
  \* input = << 3, 2, 1 >>,
  output = << >>

begin
sort:
  output := MergeSort(input);
check:
  print( << "test", input, output >> );
  assert( Len(output) = Len(input) );
  assert IsSorted(output);

  

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8662fcdf" /\ chksum(tla) = "7d9d5b3a")
VARIABLES ThisMax, input, output, pc

vars == << ThisMax, input, output, pc >>

Init == (* Global variables *)
        /\ ThisMax \in 1..MaxValue
        /\ input \in PermutationKey(ThisMax)
        /\ output = << >>
        /\ pc = "sort"

sort == /\ pc = "sort"
        /\ output' = MergeSort(input)
        /\ pc' = "check"
        /\ UNCHANGED << ThisMax, input >>

check == /\ pc = "check"
         /\ PrintT(( << "test", input, output >> ))
         /\ Assert(( Len(output) = Len(input) ), 
                   "Failure of assertion at line 56, column 3.")
         /\ Assert(IsSorted(output), 
                   "Failure of assertion at line 57, column 3.")
         /\ pc' = "Done"
         /\ UNCHANGED << ThisMax, input, output >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == sort \/ check
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
