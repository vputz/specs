// this is meant to model caching of resources with a time to live
// and a periodic process which refreshes them so that queries are
// quick.

open util/ordering[Time]

sig Time {}

sig Value {}

one sig Entry { 
  var v: one Value,
  var t: one Time
}

one sig entry in Entry {}
var sig currentTime in Time {}

pred init {
  currentTime = first
  entry.t = currentTime
}

pred refresh  {
  entry.t.next.lt[ currentTime ] => entry.t' = currentTime else entry.t' = entry.t
  //entry.v' = entry.v and entry.t' = entry.t
}

// seems like almost always you want if-then-else because an unhandled
// predicate evaluates as true... ?
pred tick {
  currentTime = last implies currentTime' = last else currentTime' = next[currentTime]
}

fact traces {
  init 
  always (tick and refresh)
//    (tick and refresh)

  
}

assert toEnd {
  eventually currentTime = last
}

//check toEnd for 3 but 7 Time, 8 steps
run {} for 7 but 4 int, 4 seq, 8 steps expect 1
