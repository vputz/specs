// this is meant to model caching of resources with a time to live
// and a periodic process which refreshes them so that queries are
// quick.  The case study is the AwsDevice devices returned from a
// braket query; the query takes 2.5s or so, so we'd like to cache them

open util/ordering[Time]

sig Time {}

sig Value {}

// this portion represents the "actual" value, which changes
// periodically
var sig current_value in Value {}

pred new_value {
  some v: Value | current_value' = v
}

pred nop_value {
  current_value' = current_value
}


// this represents the cache itself, which starts out unset and
// periodically refreshes (through a scheduled celery task, say).
sig Entry { 
  var v: lone Value,
  var t: lone Time
}

one sig cache in Entry {}

// this represents the "process" entry (the last value gotten by
// the process).  We don't actually need to store this but it's here
// for modeling purposes.
one sig process_entry in Entry {
}

// The entry (cached) and the process_entry information used by the
// process) are different things, even though they could point to the
// same information
fact distinct_entries {
  cache != process_entry
  all e: Entry | e in process_entry+cache
}

// For the process and the cache, you set the "time of retrieval"
// when you get the value
fact assignment_comes_with_time {
  all e: Entry | e.v = none iff e.t = none
}

// the currentTime advances in an ordered fashion
var sig currentTime in Time {}

// is this entry uninitialized?
pred uninitialized_entry [e: Entry] {
  e.t = none
  e.v = none
}

// is this entry out of date?
pred expired_entry[e: Entry] {
  e.t.next.lt[ currentTime]
}

// we start at the current time with a new "actual" value 
// (so that it's not unset).  The cache and process are
// uninitialized
pred init {
  currentTime = first
  new_value
  uninitialized_entry[cache]
  uninitialized_entry[process_entry]
}

// this sets the cache to a new value and time
pred set_entry[e: Entry, new_v: Value, new_t: Time] {
  e.v' = new_v and e.t' = new_t
}

// a "no operation"
pred nop_entry [e: Entry] {
  set_entry[e, e.v, e.t]
}

pred refresh_cache  {
  (uninitialized_entry[cache] or expired_entry[cache]) =>
//    v2 != entry.v 
    set_entry[cache, current_value, currentTime] else nop_entry[cache]
  //entry.v' = entry.v and entry.t' = entry.t
}

// rough simulation that the value returned is still "valid" in that
// one can create an object using it
pred valid_entry [e: Entry] {
  e.v != none
  e.v = current_value
}

pred process_get {
  // if the cache has an entry, and the entry is valid, use the entry
  valid_entry[cache] => set_entry[process_entry, cache.v, cache.t]
    // otherwise (say, creating the backend failed), get the current value, set the cache,
    // and use the current value
    else (set_entry[cache, current_value, currentTime] and set_entry[process_entry, current_value, currentTime])
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
  always (process_get or nop_entry[process_entry])
//    (tick and refresh)

  
}

assert toEnd {
  eventually currentTime = last
}

//check toEnd for 3 but 7 Time, 8 steps
run {} for 7 but 4 int, exactly 3 Value, 4 seq, 8 steps expect 1
