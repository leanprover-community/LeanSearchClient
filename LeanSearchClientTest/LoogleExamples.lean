import LeanSearchClient.Syntax

/-!
# Moogle Examples

Examples of using the Loogle API. The search is triggered when the sentence ends with a full stop (period) or a question mark. The final character (`.` or `?`) is omitted in the query.
-/

/--
warning: #loogle query should end with a `.` or `?`.
Note this command sends your query to an external service at https://loogle.lean-lang.org/json.
-/
#guard_msgs in
#loogle "List ?a → ?a"

/--
warning: #loogle query should end with a `.` or `?`.
Note this command sends your query to an external service at https://loogle.lean-lang.org/json.
-/
#guard_msgs in
example := #loogle "List ?a → ?a"


set_option loogle.queries 1

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : 3 ≤ 5 := by
  #loogle "List ?a = ?b."
  sorry
