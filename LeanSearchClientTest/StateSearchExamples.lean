import LeanSearchClient.Syntax

/-!
# LeanStateSearch Examples

Examples of using LeanStateSearch API. The search is triggered by the
tactic `#statesearch`.
-/

set_option statesearch.queries 1 -- set the number of results to 6
set_option statesearch.revision "v4.16.0" -- set the revision to v4.16.0


/-- info: Try these:
• #check Int.one_pos
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 0 < 1 := by
  #statesearch
  sorry

set_option statesearch.queries 6

/--
info: From: Nat.zero_lt_one (type: 0 < 1)
• apply Nat.zero_lt_one
• have : 0 < 1 := Nat.zero_lt_one
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 0 < 1 := by
  #statesearch
  sorry

set_option statesearch.revision "v4.15.0"

/-- error: error: "Invalid parameter value"
description: "Lean State Search does not support the specified revision"
-/
#guard_msgs in
example : 0 ≤ 1 := by
  #statesearch

/-!
Tests using `search` with `statesearch` as the backend.
-/
set_option statesearch.queries 1 -- set the number of results to 6
set_option statesearch.revision "v4.16.0" -- set the revision to v4.16.0


/-- info: Try these:
• #check Int.one_pos
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 0 < 1 := by
  #search
  sorry

set_option statesearch.queries 6

/--
info: From: Nat.zero_lt_one (type: 0 < 1)
• apply Nat.zero_lt_one
• have : 0 < 1 := Nat.zero_lt_one
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 0 < 1 := by
  #search
  sorry

set_option statesearch.revision "v4.15.0"

/-- error: error: "Invalid parameter value"
description: "Lean State Search does not support the specified revision"
-/
#guard_msgs in
example : 0 ≤ 1 := by
  #search
