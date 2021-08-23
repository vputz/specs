open util/ordering [Time]

sig Time {}

var sig currentTime in Time {}

pred init {
  currentTime = first
}

pred tick {
  currentTime != last => currentTime' = currentTime.next else currentTime' = currentTime
}

fact traces {
  init
  always tick
}
