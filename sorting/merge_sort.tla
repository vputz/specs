---- MODULE merge_sort ----

EXTENDS Sequences, Naturals, TLC, Sorting

CONSTANTS

MaxValue

(* --algorithm MergeSort

(* In this version, we'll follow Cormen et al in Algorithms, where they write

We merge by calling an auxiliary procedure
MERGE (A, p, q, r), where A is an array and p, q, and r are indices into the array
such that p <= q < r. The procedure assumes that the subarrays A[p..q] and
A[q+1 .. r] are in sorted order. It merges them to form a single sorted subarray
that replaces the current subarray A[p..r]
*)

variables
  ThisMax \in 1..MaxValue,
  input \in PermutationKey(ThisMax),
  \* input = << 3, 2, 1 >>,
  output = << >>;

\* We'll use a procedure here so that we can declare L and R;
\* In general we'd use macros, but the internal variables simplify things
\* since p <= q < r, the element referred to by q is in L and not R
\*
\* Also note that procedures do not and cannot change their arguments, so
\* you must assign things to a global variable if you need, which is why
\* we assign to output and do not pass it in
procedure Merge(p, q, r)
(* Lesson learned: from the p-manual pg 27 or thereabouts:

There is an implicit label Error immediately
after the body. If control ever reaches that point, then execution of either
the process (multiprocess algorithm) or the complete algorithm (uniprocess
algorithm) halts.

It does this quite silently and results in very weird errors
*)
variables L = << >>, R = << >>, n1, n2, i=1, j=1, k=p;
begin
  checkInputs:
  assert IsSorted(SubSeq(output, p,q));
  assert IsSorted(SubSeq(output, q+1, r));
  setLengths:
  print(<< "Merge", output, p, q, r >>);
    n1 := q-p+1;
    n2 := r-q;
  copyArrays:
    L := SubSeq(output, p, q);
    R := SubSeq(output, q+1, r);
  addSentinels:
    L := Append(L, MaxValue+1);
    R := Append(R, MaxValue+1);
  merge_merge:
    \* Often we want to avoid loops to avoid state space explosion, but here
    \* we're adhering to the book for initial clarity
    while k <= r do
      if L[i] < R[j] then
        \* this is how to replace a mapping in a function with :> and @@
	\* I believe that @@ prefers the assignment on the left
        output := (k :> L[i]) @@ output;
	print(<< "lk", k, output >>);
	i := i+1;
      else
        output := (k :> R[j]) @@ output;
	print(<< "rk", k, output >>);
	j := j+1;
      end if;
      k := k + 1;
    end while;
  assert IsSorted(SubSeq(output, p, r));
  return;
end procedure;

procedure MergeSort(p, r)
variables q;
begin
  mergesort_merge:
  print(<< "MergeSort", output, p, r >>);
  if p < r then
    \* tla+ uses \div rather than / which is available in reals
    q := (p+r) \div 2;
  sort_left:
    print("Sort left");
    call MergeSort(p, q);
  sort_right:
    print("Sort right");
    call MergeSort(q+1, r);
  merge_halves:
    call Merge(p, q, r);
  done_merging:
    skip;
\*    q := 0;
  end if;
  done_mergesort:
  return;
end procedure;

begin
sort:
  print("1test");
  print(<< "2", input >>);
  output := input;
  print("3");
  call MergeSort(1, Len(output));
check:
  print(<< "test", input, output >>);
  assert Len(output) = Len(input);
  \* should we also verify that every element in input exists in output?
  assert IsSorted(output);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4ed6d8a4" /\ chksum(tla) = "6b3b675f")
\* Procedure variable q of procedure MergeSort at line 80 col 11 changed to q_
\* Parameter p of procedure Merge at line 33 col 17 changed to p_
\* Parameter r of procedure Merge at line 33 col 23 changed to r_
CONSTANT defaultInitValue
VARIABLES ThisMax, input, output, pc, stack, p_, q, r_, L, R, n1, n2, i, j, k, 
          p, r, q_

vars == << ThisMax, input, output, pc, stack, p_, q, r_, L, R, n1, n2, i, j, 
           k, p, r, q_ >>

Init == (* Global variables *)
        /\ ThisMax \in 1..MaxValue
        /\ input \in PermutationKey(ThisMax)
        /\ output = << >>
        (* Procedure Merge *)
        /\ p_ = defaultInitValue
        /\ q = defaultInitValue
        /\ r_ = defaultInitValue
        /\ L = << >>
        /\ R = << >>
        /\ n1 = defaultInitValue
        /\ n2 = defaultInitValue
        /\ i = 1
        /\ j = 1
        /\ k = p_
        (* Procedure MergeSort *)
        /\ p = defaultInitValue
        /\ r = defaultInitValue
        /\ q_ = defaultInitValue
        /\ stack = << >>
        /\ pc = "sort"

checkInputs == /\ pc = "checkInputs"
               /\ Assert(IsSorted(SubSeq(output, p_,q)), 
                         "Failure of assertion at line 46, column 3.")
               /\ Assert(IsSorted(SubSeq(output, q+1, r_)), 
                         "Failure of assertion at line 47, column 3.")
               /\ pc' = "setLengths"
               /\ UNCHANGED << ThisMax, input, output, stack, p_, q, r_, L, R, 
                               n1, n2, i, j, k, p, r, q_ >>

setLengths == /\ pc = "setLengths"
              /\ PrintT((<< "Merge", output, p_, q, r_ >>))
              /\ n1' = q-p_+1
              /\ n2' = r_-q
              /\ pc' = "copyArrays"
              /\ UNCHANGED << ThisMax, input, output, stack, p_, q, r_, L, R, 
                              i, j, k, p, r, q_ >>

copyArrays == /\ pc = "copyArrays"
              /\ L' = SubSeq(output, p_, q)
              /\ R' = SubSeq(output, q+1, r_)
              /\ pc' = "addSentinels"
              /\ UNCHANGED << ThisMax, input, output, stack, p_, q, r_, n1, n2, 
                              i, j, k, p, r, q_ >>

addSentinels == /\ pc = "addSentinels"
                /\ L' = Append(L, MaxValue+1)
                /\ R' = Append(R, MaxValue+1)
                /\ pc' = "merge_merge"
                /\ UNCHANGED << ThisMax, input, output, stack, p_, q, r_, n1, 
                                n2, i, j, k, p, r, q_ >>

merge_merge == /\ pc = "merge_merge"
               /\ IF k <= r_
                     THEN /\ IF L[i] < R[j]
                                THEN /\ output' = (k :> L[i]) @@ output
                                     /\ PrintT((<< "lk", k, output' >>))
                                     /\ i' = i+1
                                     /\ j' = j
                                ELSE /\ output' = (k :> R[j]) @@ output
                                     /\ PrintT((<< "rk", k, output' >>))
                                     /\ j' = j+1
                                     /\ i' = i
                          /\ k' = k + 1
                          /\ pc' = "merge_merge"
                          /\ UNCHANGED << stack, p_, q, r_, L, R, n1, n2 >>
                     ELSE /\ Assert(IsSorted(SubSeq(output, p_, r_)), 
                                    "Failure of assertion at line 75, column 3.")
                          /\ pc' = Head(stack).pc
                          /\ L' = Head(stack).L
                          /\ R' = Head(stack).R
                          /\ n1' = Head(stack).n1
                          /\ n2' = Head(stack).n2
                          /\ i' = Head(stack).i
                          /\ j' = Head(stack).j
                          /\ k' = Head(stack).k
                          /\ p_' = Head(stack).p_
                          /\ q' = Head(stack).q
                          /\ r_' = Head(stack).r_
                          /\ stack' = Tail(stack)
                          /\ UNCHANGED output
               /\ UNCHANGED << ThisMax, input, p, r, q_ >>

Merge == checkInputs \/ setLengths \/ copyArrays \/ addSentinels
            \/ merge_merge

mergesort_merge == /\ pc = "mergesort_merge"
                   /\ PrintT((<< "MergeSort", output, p, r >>))
                   /\ IF p < r
                         THEN /\ q_' = ((p+r) \div 2)
                              /\ pc' = "sort_left"
                         ELSE /\ pc' = "done_mergesort"
                              /\ q_' = q_
                   /\ UNCHANGED << ThisMax, input, output, stack, p_, q, r_, L, 
                                   R, n1, n2, i, j, k, p, r >>

sort_left == /\ pc = "sort_left"
             /\ PrintT(("Sort left"))
             /\ /\ p' = p
                /\ r' = q_
                /\ stack' = << [ procedure |->  "MergeSort",
                                 pc        |->  "sort_right",
                                 q_        |->  q_,
                                 p         |->  p,
                                 r         |->  r ] >>
                             \o stack
             /\ q_' = defaultInitValue
             /\ pc' = "mergesort_merge"
             /\ UNCHANGED << ThisMax, input, output, p_, q, r_, L, R, n1, n2, 
                             i, j, k >>

sort_right == /\ pc = "sort_right"
              /\ PrintT(("Sort right"))
              /\ /\ p' = q_+1
                 /\ r' = r
                 /\ stack' = << [ procedure |->  "MergeSort",
                                  pc        |->  "merge_halves",
                                  q_        |->  q_,
                                  p         |->  p,
                                  r         |->  r ] >>
                              \o stack
              /\ q_' = defaultInitValue
              /\ pc' = "mergesort_merge"
              /\ UNCHANGED << ThisMax, input, output, p_, q, r_, L, R, n1, n2, 
                              i, j, k >>

merge_halves == /\ pc = "merge_halves"
                /\ /\ p_' = p
                   /\ q' = q_
                   /\ r_' = r
                   /\ stack' = << [ procedure |->  "Merge",
                                    pc        |->  "done_merging",
                                    L         |->  L,
                                    R         |->  R,
                                    n1        |->  n1,
                                    n2        |->  n2,
                                    i         |->  i,
                                    j         |->  j,
                                    k         |->  k,
                                    p_        |->  p_,
                                    q         |->  q,
                                    r_        |->  r_ ] >>
                                \o stack
                /\ L' = << >>
                /\ R' = << >>
                /\ n1' = defaultInitValue
                /\ n2' = defaultInitValue
                /\ i' = 1
                /\ j' = 1
                /\ k' = p_'
                /\ pc' = "checkInputs"
                /\ UNCHANGED << ThisMax, input, output, p, r, q_ >>

done_merging == /\ pc = "done_merging"
                /\ TRUE
                /\ pc' = "done_mergesort"
                /\ UNCHANGED << ThisMax, input, output, stack, p_, q, r_, L, R, 
                                n1, n2, i, j, k, p, r, q_ >>

done_mergesort == /\ pc = "done_mergesort"
                  /\ pc' = Head(stack).pc
                  /\ q_' = Head(stack).q_
                  /\ p' = Head(stack).p
                  /\ r' = Head(stack).r
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << ThisMax, input, output, p_, q, r_, L, R, n1, 
                                  n2, i, j, k >>

MergeSort == mergesort_merge \/ sort_left \/ sort_right \/ merge_halves
                \/ done_merging \/ done_mergesort

sort == /\ pc = "sort"
        /\ PrintT(("1test"))
        /\ PrintT((<< "2", input >>))
        /\ output' = input
        /\ PrintT(("3"))
        /\ /\ p' = 1
           /\ r' = Len(output')
           /\ stack' = << [ procedure |->  "MergeSort",
                            pc        |->  "check",
                            q_        |->  q_,
                            p         |->  p,
                            r         |->  r ] >>
                        \o stack
        /\ q_' = defaultInitValue
        /\ pc' = "mergesort_merge"
        /\ UNCHANGED << ThisMax, input, p_, q, r_, L, R, n1, n2, i, j, k >>

check == /\ pc = "check"
         /\ PrintT((<< "test", input, output >>))
         /\ Assert(Len(output) = Len(input), 
                   "Failure of assertion at line 112, column 3.")
         /\ Assert(IsSorted(output), 
                   "Failure of assertion at line 114, column 3.")
         /\ pc' = "Done"
         /\ UNCHANGED << ThisMax, input, output, stack, p_, q, r_, L, R, n1, 
                         n2, i, j, k, p, r, q_ >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Merge \/ MergeSort \/ sort \/ check
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
