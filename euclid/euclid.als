
sig Pair {
  var x: Int, 
  var y: Int
}

fact {
  univ.x > 0
  univ.y > 0
}

pred step [p: Pair] {
  p.x != p.y =>
    (p.x > p.y => p.x' = sub[p.x, p.y] and p.y' = p.y else p.x' = p.x and p.y' = sub[p.y,p.x])
  else p.x' = p.x and p.y' = p.y
}

//pred astep [p: Pair] {
//  p.x != p.y => (p.x > p.y => (p.x' = p.y and p.y' = p.x))
//}

pred skip {
  x' = x
  y' = y
}

enum Event { Step, Skip }

fun _step : Event -> Pair {
  Step -> { p : Pair | step[p] }
}

fun _skip : Event {
  { e: Skip | skip }
}

fun events : set Event {
  (_step).Pair + _skip
}

pred example {
  some p: Pair | p.x=32 and p.y=18
 always (skip or all p: Pair | step[p])
 eventually some p: Pair | p.x=p.y
}

run example for 8 but exactly 1 Pair, 7 int
