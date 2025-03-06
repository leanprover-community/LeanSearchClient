import LeanSearchClient.Syntax

/-!
# LeanStateSearch Examples

Examples of using LeanStateSearch API. The search is triggered by the
tactic `#statesearch`.
-/

set_option statesearch.queries 1

/-- info: Try these:
• #check Int.one_nonneg
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 1 ≤ 0 := by
  #statesearch "v4.16.0"
  sorry

/-- error: Could not obtain array from {"schema":
 {"description": "Lean State Search does not support the specified revision"},
 "error": "Invalid parameter value"}; error: array expected
-/
#guard_msgs in
example : 1 ≤ 0 := by
  #statesearch "v4.15.0"

/-- info: Try these:
• #check Int.one_nonneg
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 1 ≤ 0 := by
  #statesearch
  sorry
