import LeanSearchClient.Syntax

/-!
# Lean Search Examples

Examples of using the leansearch API. The search is triggered when the sentence ends with a full stop (period) or a question mark.
-/

/--
warning: #leansearch query should end with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

/--
warning: #leansearch query should end with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

set_option leansearch.queries 1

/--
info: From: Nat.succ_lt_succ (type: ∀ {n m : Nat}, n < m → Nat.succ n < Nat.succ m)
• apply Nat.succ_lt_succ
• have : ∀ {n m : Nat}, n < m → Nat.succ n < Nat.succ m := Nat.succ_lt_succ
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
