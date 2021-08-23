// modeling leader election as per the ELectrum tutorial,
// https://github.com/haslab/Electrum/wiki/Tutorial

open util/ordering[Id]

sig Id {}

sig Process {
  succ: Process,
  var toSend: set Id,
  id : Id
}

fact distinctIds {
  id in Process lone -> Id
}

fact ring {
  all p: Process | Process in p.^succ
}

var sig elected in Process {}

// Then, at every instant, the set will contain in the next instant
// processes that will just have received their own identifier (i.e.
// they don't hold it the current instant):
fact defineElected {
  no elected // empty in initial state
  always elected' = { p : Process | (after p.id in p.toSend) and p.id !in p.toSend }
}

pred communication [p: Process] {
  some identifier: p.toSend {
    p.toSend' = p.toSend - identifier
    p.succ.toSend' = p.succ.toSend + (identifier - prevs[p.succ.id])
  }
}

pred init {
  all p: Process | p.toSend = p.id
}

pred doNothing [p: Process] { p.toSend' = p.toSend }

fact traces {
  init
  always all p: Process | communication[p] or communication[p.~succ] or doNothing [p] 
}

assert Safety {
  always all x: elected | always all y : elected | x = y
}

assert Liveness1 {
  some Process => eventually some elected
}

//One solution is to force communication to happen at every step if it's possible. 
//This can be specified as a progress property that says that, as long as there is a
// non-empty buffer for some process, then at the next instant, at least one 
//process won't do nothing. Executing this command yields no counterexample.

pred progress {
  always (some Process.toSend => after some p: Process | not doNothing[p])
}

assert Liveness2 {
  (some Process && progress) => eventually some elected 
}

//check Safety for 3 but 20 steps
//check Liveness1 for 3 but 20 steps
//check Liveness2 for 3 but 20 steps
run progress for 7 but exactly 3 Process, 5 steps
//check Safety for 3 but 1.. steps
