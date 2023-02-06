---- MODULE maximum_subarray ----

EXTENDS Sequences, Integers, TLC

CONSTANTS

MaxSequenceLength,
MinValue,
MaxValue

(* We can generate a set of all possible sequences of all our values.
This can get out of hand fast, but for small entries of MinValue,
MaxValue, and MaxSequenceLength it can be tractable.  You could also
set a MinSequenceLength, have the Values be a set, etc. *)

Values == MinValue..MaxValue
Lengths == 1..MaxSequenceLength

(* We can generate all possible sets of indices pretty easily *)

AllIndices == { 1..n : n \in Lengths }

(* but mapping those to values gets us a set of sets... *)
SequenceSet == {[indices -> Values] : indices \in AllIndices}

(* so to get all sequences we need to join those sets *)
RECURSIVE MergeSets(_,_)

MergeSets(sets, setofsets) ==
  IF setofsets = {} THEN sets
  ELSE LET newmember == CHOOSE x \in setofsets: TRUE IN
    MergeSets(sets \union newmember, setofsets \ {newmember})

MergeSetOfSets(setofsets) ==
  MergeSets( {}, setofsets )

AllSequences == MergeSetOfSets(SequenceSet)

AllIntervals(s) == { SubSeq(s, i, j): i,j \in 1..Len(s) }

RECURSIVE SeqSum(_)
SeqSum(s) ==
  IF s = << >> THEN 0 ELSE
    LET
      h == Head(s)
      t == Tail(s) IN
    h + SeqSum(t)

(* Much of that was to generate this, which finds the maximum subsequence by exhaustive
search, creating the set of all maximum subsequences of a sequence and locating the
one with the maximum value.  This is not the most efficient way of doing this of course,
but it sets up the checking for the algorithm which we will implement in pluscal
according to the book. *)
MaxSubSeq(s) ==
  LET intervals == AllIntervals(s) IN
    CHOOSE result \in intervals: \A interval \in intervals : SeqSum(result) >= SeqSum(interval)

(* --algorithm MaximumSubarray
variables
  input \in AllSequences

begin
  print(input)
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "48e63674" /\ chksum(tla) = "e196a4ba")
VARIABLES input, pc

vars == << input, pc >>

Init == (* Global variables *)
        /\ input \in AllSequences
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT((input))
         /\ pc' = "Done"
         /\ input' = input

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
