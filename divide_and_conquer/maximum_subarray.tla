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

AllIntervals(s) == LET S == 1..Len(s) IN
  { << i,j >> \in S \X S: i <= j }

AllSubSequences(s) == { SubSeq(s, x[1], x[2]): x \in AllIntervals(s) }


RECURSIVE SeqSum(_)
SeqSum(s) ==
  IF s = << >> THEN 0 ELSE
    LET
      h == Head(s)
      t == Tail(s) IN
    h + SeqSum(t)

IntervalSum(s, interval) ==
  SeqSum(SubSeq(s, interval[1], interval[2]))

(* Much of that was to generate this, which finds the maximum subsequence by exhaustive
search, creating the set of all maximum subsequences of a sequence and locating the
one with the maximum value.  This is not the most efficient way of doing this of course,
but it sets up the checking for the algorithm which we will implement in pluscal
according to the book. *)
MaxInterval(s, intervals) ==
  CHOOSE x \in intervals: \A interval \in intervals \ {x} :
    IntervalSum(s, x) >= IntervalSum(s, interval) 

MaxSeqInterval(s) ==
  LET intervals == AllIntervals(s)
      maxInterval == MaxInterval(s, intervals)
  IN << maxInterval[1], maxInterval[2], IntervalSum(s, maxInterval) >>


MaxCrossingInterval(s, low, mid, high) ==
  LET leftIntervals == { << i, mid >> : i \in low..mid }
      rightIntervals == { << mid+1, j >> : j \in mid+1 .. high }
      maxLeftInterval == MaxInterval(s, leftIntervals)
      leftIntervalSum == IntervalSum(s, maxLeftInterval)
      maxRightInterval == MaxInterval(s, rightIntervals)
      rightIntervalSum == IntervalSum(s, maxRightInterval)
  IN
    << maxLeftInterval[1], maxRightInterval[2], leftIntervalSum + rightIntervalSum >>

RECURSIVE FindMaximumSubarray(_,_,_)

FindMaximumSubarray(s, low, high) ==
  IF low = high
  THEN << low, high, s[low] >>
  ELSE
    LET mid == (low+high) \div 2
        maxLeft == FindMaximumSubarray(s, low, mid)
	maxRight == FindMaximumSubarray(s, mid+1, high)
	maxCross == MaxCrossingInterval(s, low, mid, high)
    IN
      CASE maxLeft[3] >= maxRight[3] /\ maxLeft[3] >= maxCross[3] -> maxLeft
        []  maxRight[3] >= maxLeft[3] /\ maxRight[3] >= maxCross[3] -> maxRight
	[]  OTHER -> maxCross

(* --algorithm MaximumSubarray
variables
  input \in AllSequences,
  foundMax,
  calcMax;

begin
CALC:
  foundMax := FindMaximumSubarray(input, 1, Len(input));
  calcMax := MaxSeqInterval(input);
CHECK:
  \* For purposes of this exercise, which is just familiarity with TLA+, we'll presently
  \* just check that the sums are equal--that we have found *a* maximum subsequence.
  \* These are not guaranteed to be the same as the calculated one since we need additional
  \* criteria (smallest length, earliest appearing) to make them equal--which we can
  \* do, but it's beyond the point of this exercise
  assert foundMax[3] = calcMax[3];
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "fbdc1ddb" /\ chksum(tla) = "f476a4f5")
CONSTANT defaultInitValue
VARIABLES input, foundMax, calcMax, pc

vars == << input, foundMax, calcMax, pc >>

Init == (* Global variables *)
        /\ input \in AllSequences
        /\ foundMax = defaultInitValue
        /\ calcMax = defaultInitValue
        /\ pc = "CALC"

CALC == /\ pc = "CALC"
        /\ foundMax' = FindMaximumSubarray(input, 1, Len(input))
        /\ calcMax' = MaxSeqInterval(input)
        /\ pc' = "CHECK"
        /\ input' = input

CHECK == /\ pc = "CHECK"
         /\ Assert(foundMax[3] = calcMax[3], 
                   "Failure of assertion at line 112, column 3.")
         /\ pc' = "Done"
         /\ UNCHANGED << input, foundMax, calcMax >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CALC \/ CHECK
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
