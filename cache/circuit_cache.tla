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

EXTENDS Naturals, TLC

     JOBS == 2..4
     RESULTS == 2..4

(* --algorithm add
  variables
  submission_cache = << >>;
  remaining_jobs = JOBS;
  next_job = 0;
  next_job_id = 0; \* this is increased with each
  
  \* macros here
macro submit_job(j) begin
  submission_cache := submission_cache @@ j :> next_job_id;
  next_job_id := next_job_id+1;
  remaining_jobs := remaining_jobs \ {j};
  \* add an either clause so that some submissions fail
end macro

begin
  SubmitJobs:
    while remaining_jobs # {} do
      next_job := CHOOSE j \in remaining_jobs: TRUE;
      print << "job", next_job >>;
      submit_job(next_job);
      print <<"cache", submission_cache, "next_job_id", next_job_id >>;
      
    end while
end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "6677de44" /\ chksum(tla) = "ac61dbd3")
VARIABLES submission_cache, remaining_jobs, next_job, next_job_id, pc

vars == << submission_cache, remaining_jobs, next_job, next_job_id, pc >>

Init == (* Global variables *)
        /\ submission_cache = << >>
        /\ remaining_jobs = JOBS
        /\ next_job = 0
        /\ next_job_id = 0
        /\ pc = "SubmitJobs"

SubmitJobs == /\ pc = "SubmitJobs"
              /\ IF remaining_jobs # {}
                    THEN /\ next_job' = (CHOOSE j \in remaining_jobs: TRUE)
                         /\ PrintT(<< "job", next_job' >>)
                         /\ submission_cache' = (submission_cache @@ next_job' :> next_job_id)
                         /\ next_job_id' = next_job_id+1
                         /\ remaining_jobs' = remaining_jobs \ {next_job'}
                         /\ PrintT(<<"cache", submission_cache', "next_job_id", next_job_id' >>)
                         /\ pc' = "SubmitJobs"
                    ELSE /\ pc' = "Done"
                         /\ UNCHANGED << submission_cache, remaining_jobs, 
                                         next_job, next_job_id >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == SubmitJobs
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
