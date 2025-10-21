module

public meta import LeanSearchClient.Syntax

public meta section

/-!
# Lean Search Examples

Examples of using the leansearch API. The search is triggered when the sentence ends with a full stop (period) or a question mark.
-/

/--
warning: #leansearch query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

/--
warning: #leansearch query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

set_option leansearch.queries 1

/--
info: From: Nat.le_of_succ_le_succ (type: ∀ {n m : Nat}, LE.le n.succ m.succ → LE.le n m)
  [apply] apply Nat.le_of_succ_le_succ
  [apply] have : ∀ {n m : Nat}, LE.le n.succ m.succ → LE.le n m := Nat.le_of_succ_le_succ
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry


/--
warning: #leansearch query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
example : 3 ≤ 5 := by
  #leansearch
  decide

/-!
# Lean Search Examples using `#search`
-/
set_option leansearchclient.backend "leansearch"

/--
warning: #leansearch query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
#search "If a natural number n is less than m, then the successor of n is less than the successor of m"

/--
warning: #leansearch query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
example := #search "If a natural number n is less than m, then the successor of n is less than the successor of m"

set_option leansearch.queries 1

/--
info: From: Nat.le_of_succ_le_succ (type: ∀ {n m : Nat}, LE.le n.succ m.succ → LE.le n m)
  [apply] apply Nat.le_of_succ_le_succ
  [apply] have : ∀ {n m : Nat}, LE.le n.succ m.succ → LE.le n m := Nat.le_of_succ_le_succ
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 3 ≤ 5 := by
  #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry


/--
warning: #leansearch query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://leansearch.net/.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 3 ≤ 5 := #search

set_option leansearchclient.backend "magic"

/-- error: Invalid backend magic, must be leansearch -/
#guard_msgs in
#search "Every slice knot is ribbon."
