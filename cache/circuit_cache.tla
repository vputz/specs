(* The idea is that we're trying to define a sort of two-level cache for
  a job system; you submit the job and get a job ID, then submit the job ID
  and get the result (the idea here is submitting quantum circuits to
  a remote evaluator like IBMQ)

  The wrinkle which will be added is that we want to be able to store metadata
  (key-value pairs) with each job such that we can set a set of keys which
  must be matched for a job submission to result in a cache hit.

  A real-world example would be a job consisting of a quantum circuit and the
  qubits to be measured.  A tag added could be an experiment name (ex1, ex2).
  Submitting (job, ex1) and (job, ex2) results in two different cache entries.

  ?? We think that setting any new metadata should result in a new cache entry

  We set the "cacheable" metadata as a set of keys which must be matched to
  result in a job cache hit.

  A cache miss on the submission should result in a resubmission to the backend.

  A cache miss on the job retrieval should result in a retrieval of the job
  from the backend

  A failure of retrieval from the backend should result in a resubmission
  *)

---- MODULE circuit_cache ----

EXTENDS Naturals, TLC, Functions, Sequences, SequencesExt

CONSTANTS NullResult, MAX_TRIES, JOBS, RESULTS

\*JOBS == 2..4
\*RESULTS == 2..4
\* The backend does the actual calculation; we could do it with a
\* dummy operation but this is more abstract
BACKEND == CHOOSE s \in Bijection(JOBS,RESULTS): TRUE


PermSeqs(S) ==
  LET seqs == SetToSeqs(S) IN
    LET s1 == CHOOSE s1 \in seqs: TRUE IN
      LET s2 == CHOOSE s2 \in seqs: s1 # s2 IN
        FlattenSeq(<< s1, s2 >>)
    
(* --algorithm add
  variables
  submission_cache = << >>;
  backend_cache = << >>;
  job_cache = << >>;
  remaining_jobs = PermSeqs(JOBS);
  next_job = 0;
  this_result = 0;
  last_job_id = 0; \* this is set to the job we just submitted (ugly?)
  next_job_id = 0; \* this is increased with each
  num_tries = 0;
  
  \* macros here
  macro submit_job(j) begin
    if j \in DOMAIN submission_cache then
    last_job_id := submission_cache[j];
    print << "Submission hit" >>;
  else
    print << "Submission miss" >>;
    submission_cache := submission_cache @@ j :> next_job_id;
    \* add a reverse entry for the backend showing it got the job
    \* and can process it; this may be "either"ed
    \* because the backend may not process the job
    either 
      backend_cache := backend_cache @@ next_job_id :> j;
    or
      skip;
    end either;
    last_job_id := next_job_id;
    next_job_id := next_job_id+1;
  end if
  \* add an either clause so that some submissions fail
end macro

macro retrieve_result(jid) begin
  if jid \in DOMAIN job_cache then
    this_result := job_cache[jid];
    print << "Retrieval hit" >>;
  else
    if jid \in DOMAIN backend_cache then
      print << "Retrieval miss" >>;
      this_result := BACKEND[backend_cache[jid]];
      job_cache := job_cache @@ jid :> this_result;
    else
      this_result := NullResult
    end if
  end if
end macro

begin
  SubmitJobs:
    while Len(remaining_jobs) > 0 do
      num_tries := 0;
      this_result := NullResult;
      DoJob:
      while ((num_tries < MAX_TRIES) /\ (this_result = NullResult)) do
        next_job := Head(remaining_jobs);
        num_tries := num_tries + 1;
        SubmitJob:
          print << "job", next_job, "num_tries", num_tries >>;
          submit_job(next_job);
	  print <<"cache", submission_cache, "next_job_id", next_job_id >>;
        RetrieveJob:
          retrieve_result(last_job_id);
          \* for each submitted job we cache the result.  The backend actually
          \* is what translates the job into a result
      end while;
      remaining_jobs := Tail(remaining_jobs);
    end while
end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "e890f98a" /\ chksum(tla) = "bf076186")
VARIABLES submission_cache, backend_cache, job_cache, remaining_jobs, 
          next_job, this_result, last_job_id, next_job_id, num_tries, pc

vars == << submission_cache, backend_cache, job_cache, remaining_jobs, 
           next_job, this_result, last_job_id, next_job_id, num_tries, pc >>

Init == (* Global variables *)
        /\ submission_cache = << >>
        /\ backend_cache = << >>
        /\ job_cache = << >>
        /\ remaining_jobs = PermSeqs(JOBS)
        /\ next_job = 0
        /\ this_result = 0
        /\ last_job_id = 0
        /\ next_job_id = 0
        /\ num_tries = 0
        /\ pc = "SubmitJobs"

SubmitJobs == /\ pc = "SubmitJobs"
              /\ IF Len(remaining_jobs) > 0
                    THEN /\ num_tries' = 0
                         /\ this_result' = NullResult
                         /\ pc' = "DoJob"
                    ELSE /\ pc' = "Done"
                         /\ UNCHANGED << this_result, num_tries >>
              /\ UNCHANGED << submission_cache, backend_cache, job_cache, 
                              remaining_jobs, next_job, last_job_id, 
                              next_job_id >>

DoJob == /\ pc = "DoJob"
         /\ IF ((num_tries < MAX_TRIES) /\ (this_result = NullResult))
               THEN /\ next_job' = Head(remaining_jobs)
                    /\ num_tries' = num_tries + 1
                    /\ pc' = "SubmitJob"
                    /\ UNCHANGED remaining_jobs
               ELSE /\ remaining_jobs' = Tail(remaining_jobs)
                    /\ pc' = "SubmitJobs"
                    /\ UNCHANGED << next_job, num_tries >>
         /\ UNCHANGED << submission_cache, backend_cache, job_cache, 
                         this_result, last_job_id, next_job_id >>

SubmitJob == /\ pc = "SubmitJob"
             /\ PrintT(<< "job", next_job, "num_tries", num_tries >>)
             /\ IF next_job \in DOMAIN submission_cache
                   THEN /\ last_job_id' = submission_cache[next_job]
                        /\ PrintT(<< "Submission hit" >>)
                        /\ UNCHANGED << submission_cache, backend_cache, 
                                        next_job_id >>
                   ELSE /\ PrintT(<< "Submission miss" >>)
                        /\ submission_cache' = (submission_cache @@ next_job :> next_job_id)
                        /\ \/ /\ backend_cache' = (backend_cache @@ next_job_id :> next_job)
                           \/ /\ TRUE
                              /\ UNCHANGED backend_cache
                        /\ last_job_id' = next_job_id
                        /\ next_job_id' = next_job_id+1
             /\ PrintT(<<"cache", submission_cache', "next_job_id", next_job_id' >>)
             /\ pc' = "RetrieveJob"
             /\ UNCHANGED << job_cache, remaining_jobs, next_job, this_result, 
                             num_tries >>

RetrieveJob == /\ pc = "RetrieveJob"
               /\ IF last_job_id \in DOMAIN job_cache
                     THEN /\ this_result' = job_cache[last_job_id]
                          /\ PrintT(<< "Retrieval hit" >>)
                          /\ UNCHANGED job_cache
                     ELSE /\ IF last_job_id \in DOMAIN backend_cache
                                THEN /\ PrintT(<< "Retrieval miss" >>)
                                     /\ this_result' = BACKEND[backend_cache[last_job_id]]
                                     /\ job_cache' = (job_cache @@ last_job_id :> this_result')
                                ELSE /\ this_result' = NullResult
                                     /\ UNCHANGED job_cache
               /\ pc' = "DoJob"
               /\ UNCHANGED << submission_cache, backend_cache, remaining_jobs, 
                               next_job, last_job_id, next_job_id, num_tries >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == SubmitJobs \/ DoJob \/ SubmitJob \/ RetrieveJob
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
