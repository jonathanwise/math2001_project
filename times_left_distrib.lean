import natural_numbers
import times_comm
import times_right_distrib

theorem times_left_distrib ( m n p : ℕ )
: m * ( n + p ) = m*n + m*p := by
  rewrite[times_comm,times_right_distrib,times_comm m n, times_comm p m]
  rfl
