import LeanSearchClient.Syntax

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
info: LeanSearch: [{"result":
  {"value": ":=\n  ⟨succ_lt_succ l.h⟩",
   "type": "∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ",
   "signature": " (m n) [l : IsLT m n] : IsLT (succ m) (succ n)",
   "name": ["Fin2", "IsLT", "succ"],
   "module_name": ["Mathlib", "Data", "Fin", "Fin2"],
   "kind": "instance",
   "informal_name": "Successor preserves the less-than relation for natural numbers",
   "informal_description":
   "For natural numbers $m$ and $n$, if $m < n$ holds, then $\\mathrm{succ}(m) < \\mathrm{succ}(n)$ also holds.",
   "docstring": null},
  "distance": 0.0862322449684143}]
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
info: LeanSearch: [{"result":
  {"value": ":=\n  ⟨succ_lt_succ l.h⟩",
   "type": "∀ (m n : ℕ) [l : Fin2.IsLT m n], Fin2.IsLT m.succ n.succ",
   "signature": " (m n) [l : IsLT m n] : IsLT (succ m) (succ n)",
   "name": ["Fin2", "IsLT", "succ"],
   "module_name": ["Mathlib", "Data", "Fin", "Fin2"],
   "kind": "instance",
   "informal_name": "Successor preserves the less-than relation for natural numbers",
   "informal_description":
   "For natural numbers $m$ and $n$, if $m < n$ holds, then $\\mathrm{succ}(m) < \\mathrm{succ}(n)$ also holds.",
   "docstring": null},
  "distance": 0.0862322449684143}]
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

/-- error: Invalid backend magic, should be one of leansearch and moogle -/
#guard_msgs in
#search "Every slice knot is ribbon."
