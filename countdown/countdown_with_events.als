// Trying to learn how to do state machines from https://alloytools.discourse.group/t/modelling-a-state-machine-in-electrum-towards-alloy-6/88
//open util/integers

sig State {
  // must declare things as 'var'
  // see tutorial https://github.com/haslab/Electrum/wiki/Tutorial
  var x: Int
}

// Events are introduced as predicates.  They may have
// - a guard saying when the event can happen
// - An effect on some/all state variables (sigs and fields)
// - A frame condition saying what does not change
pred countdown [s: State] {
  s.x' = sub[s.x,1]
}

pred skip {
  x' = x
}

fact behaviour {
  //some s: State | s.x = 3
  always (skip or some s: State | countdown[s])
}

enum Event { Skip, Countdown }

fun _skip : Event {
  { e: Skip | skip }
}

fun _countdown : Event -> State {
  Countdown -> { s : State | countdown[s] }
}

fun events : set Event {
  (_countdown).State + _skip
}

pred example { eventually some s: State | s.x = 0 }

run example for 6 but exactly 1 State
