import LeanSearchClient.Syntax

/-!
# Moogle Examples

Examples of using the Moogle API. The search is triggered when the sentence ends with a full stop (period) or a question mark.
-/

/--
warning: #moogle query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://www.moogle.ai/api/search.
-/
#guard_msgs in
#moogle "If a natural number n is less than m, then the successor of n is less than the successor of m"

/--
warning: #moogle query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://www.moogle.ai/api/search.
-/
#guard_msgs in
example := #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m"

set_option moogle.queries 1

/--
info: From: Nat.lt (type: Nat → Nat → Prop)
• have : Nat → Nat → Prop := Nat.lt
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 3 ≤ 5 := by
  #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
