// this is meant to model caching of resources with a time to live
// and a periodic process which refreshes them so that queries are
// quick.

open util/ordering[Time]

sig Time {}

sig Value {}

var sig current_value in Value {}

pred new_value {
  some v: Value | current_value' = v
}

pred nop_value {
  current_value' = current_value
}

sig Entry { 
  var v: lone Value,
  var t: lone Time
}

one sig entry in Entry {}
one sig process_entry in Entry {
}

fact distinct_entries {
  entry != process_entry
  all e: Entry | e in process_entry+entry
}

fact assignment_comes_with_time {
  all e: Entry | e.v = none iff e.t = none
}

var sig currentTime in Time {}

pred uninitialized_entry [e: Entry] {
  e.t = none
  e.v = none
}

pred init {
  currentTime = first
  new_value
  uninitialized_entry[entry]
  uninitialized_entry[process_entry]
}

pred set_cache[new_v: Value, new_t: Time] {
  entry.v' = new_v and entry.t' = new_t
}

pred nop_cache {
  set_cache[entry.v, entry.t]
}

pred refresh_cache  {
  ((entry.t = none and entry.v = none) 
    or entry.t.next.lt[ currentTime ]) =>
//    v2 != entry.v 
    set_cache[current_value, currentTime] else nop_cache
  //entry.v' = entry.v and entry.t' = entry.t
}

pred process_get {
  entry.v != none => (process_entry.v' = entry.v and process_entry.t' = entry.t)
    else (some v2: Value {process_entry.v' = v2 and process_entry.t' = currentTime})
}

pred process_nop {
  process_entry.v' = process_entry.v
  process_entry.t' = process_entry.t
}

// seems like almost always you want if-then-else because an unhandled
// predicate evaluates as true... ?
pred tick {
  currentTime = last implies currentTime' = last else currentTime' = next[currentTime]
}

fact traces {
  init 
  always (new_value or nop_value)
  always (tick and refresh_cache)
  always (process_get or process_nop)
//    (tick and refresh)

  
}

assert toEnd {
  eventually currentTime = last
}

//check toEnd for 3 but 7 Time, 8 steps
run {} for 7 but 4 int, exactly 3 Value, 4 seq, 8 steps expect 1
