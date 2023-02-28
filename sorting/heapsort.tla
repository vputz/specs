---- MODULE heapsort ----

EXTENDS Sequences, Naturals, TLC, Sorting

CONSTANTS

MaxValue

\* indexing

ParentIndex(i) == i \div 2
LeftIndex(i) == 2*i
RightIndex(i) == 2*i+1

MaxHeapProperty(s, i) == s[ParentIndex(i)] >= s[i]

\* A heap here is a structure/record mapping A to the sequence of heap
\* values, and heapsize to the "heap size"

Heap(s, heap_size) == [A |-> s, heapsize |-> heap_size]


\* instead of a recursive operator it may be better to
\* CHOOSE from the set of possible trees such that
\* the MaxHeapProperty is satisfied, but this is similar
\* to implementing sort by a similar CHOOSE
RECURSIVE MaxHeapify(_,_)

MaxHeapify(H, i) ==
  LET l == LeftIndex(i)
      r == RightIndex(i)
      candidates == {x \in {i,l,r} : x <= H.heapsize}
      largest == CHOOSE x \in candidates: \A y \in candidates \ {x} : H.A[x] > H.A[y]
  IN
    IF largest /= i THEN
      MaxHeapify(Heap([H.A EXCEPT ![i] = H.A[largest], ![largest] = H.A[i]],
                      H.heapsize), largest)
    ELSE
      H

RECURSIVE BuildMaxHeapHelper(_,_)

BuildMaxHeapHelper(H, i) ==
  IF i = 0 THEN H ELSE BuildMaxHeapHelper(MaxHeapify(H,i), i-1)


BuildMaxHeap(A) ==
  LET H == Heap(A, Len(A)) IN BuildMaxHeapHelper(H, Len(A) \div 2)


RECURSIVE HeapSortHelper(_,_)

HeapSortHelper(H, i) ==
  IF i = 1 THEN H ELSE
    LET A == [H.A EXCEPT ![i] = H.A[1], ![1] = H.A[i]]
        heap_size == H.heapsize - 1
	newH == MaxHeapify(Heap(A, heap_size), 1)
    IN
        HeapSortHelper(newH, i-1)

HeapSort(A) ==
  LET H == BuildMaxHeap(A)
  IN HeapSortHelper(H, Len(A)).A
      
(* --algorithm heapsort
variables
  ThisMax \in 1..MaxValue,
  input \in PermutationKey(ThisMax),
  \* input = << 3, 2, 1 >>,
  output = << >>;

begin
sort:
  output := HeapSort(input);
  print( << input, output >> );
  assert Len(output) = Len(input);
  assert IsSorted(output);
  

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3102fdd6" /\ chksum(tla) = "54fb2e3b")
VARIABLES ThisMax, input, output, pc

vars == << ThisMax, input, output, pc >>

Init == (* Global variables *)
        /\ ThisMax \in 1..MaxValue
        /\ input \in PermutationKey(ThisMax)
        /\ output = << >>
        /\ pc = "sort"

sort == /\ pc = "sort"
        /\ output' = HeapSort(input)
        /\ PrintT(( << input, output' >> ))
        /\ Assert(Len(output') = Len(input), 
                  "Failure of assertion at line 76, column 3.")
        /\ Assert(IsSorted(output'), 
                  "Failure of assertion at line 77, column 3.")
        /\ pc' = "Done"
        /\ UNCHANGED << ThisMax, input >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == sort
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


====
