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
  some v: Value | current_value != v and current_value' = v
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
  e.t = none and
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
  some v: Value | current_value = v
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
  e.v != none and
  e.v = current_value
}

pred process_get {
  //set_entry[process_entry, cache.v, cache.t]
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


// the behaviours.  We basically stop changing values (and ticking the clock) after the process sets an 
// entry to show in an assertion that if the process sets a value it sets the current one
// and is valid.  We try to set it so you don't get a new value when you also get a process_get
fact traces {
  init 
  always (uninitialized_entry[process_entry] implies
    (tick and ((new_value and refresh_cache and nop_entry[process_entry])) or (nop_value and process_get))
  else
    nop_value
    and nop_entry[process_entry])

//  always ((uninitialized_entry[process_entry] implies new_value else nop_value) or nop_value)
//  always (uninitialized_entry[process_entry] implies (tick and refresh_cache) else tick)
//  always ((uninitialized_entry[process_entry] implies process_get else nop_entry[process_entry]) or nop_entry[process_entry])
}

// Events!

enum Event { NewValue, NopValue, Tick, RefreshCache, ProcessGet, ProcessNop }

fun _NewValue : Event { {e: NewValue | new_value }
}

fun _NopValue : Event {{ e: NopValue | nop_value }}

fun _Tick: Event {{ t: Tick | tick }}

fun _RefreshCache: Event {{ r: RefreshCache | refresh_cache }}

fun _ProcessGet: Event {{ p: ProcessGet | process_get }}

fun events: set Event {
  _NewValue + _NopValue + _Tick + _RefreshCache + _ProcessGet
}

assert cacheEmptyOrSet {
  uninitialized_entry[cache] or (cache.t != none and cache.v != none)
}

assert setProcessEqualsCurrentValue {
 always (uninitialized_entry[process_entry] 
 or ((not uninitialized_entry[process_entry]) triggered   (process_entry.v = current_value)))
}

// check cacheEmptyOrSet for 8
check setProcessEqualsCurrentValue for 10
run {} for 7 but 4 int, exactly 3 Value, 4 seq, 8 steps expect 1
