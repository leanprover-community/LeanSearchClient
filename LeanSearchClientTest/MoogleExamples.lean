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

-- As of 2025-09-25, Moogle is down.

-- set_option moogle.queries 1 in
-- /--
-- info: From: Nat.lt (type: Nat → Nat → Prop)
-- • have : Nat → Nat → Prop := Nat.lt
-- ---
-- warning: declaration uses 'sorry'
-- -/
-- #guard_msgs in
-- example : 3 ≤ 5 := by
--   #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
--   sorry

/-!
## Moogle queries using `search`
-/

set_option leansearchclient.backend "moogle"
/--
warning: #moogle query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://www.moogle.ai/api/search.
-/
#guard_msgs in
#search "If a natural number n is less than m, then the successor of n is less than the successor of m"

/--
warning: #moogle query should be a string that ends with a `.` or `?`.
Note this command sends your query to an external service at https://www.moogle.ai/api/search.
-/
#guard_msgs in
example := #search "If a natural number n is less than m, then the successor of n is less than the successor of m"

set_option moogle.queries 1

-- As of 2025-09-25, Moogle is down.

-- /--
-- info: From: Nat.lt (type: Nat → Nat → Prop)
-- • have : Nat → Nat → Prop := Nat.lt
-- ---
-- warning: declaration uses 'sorry'
-- -/
-- #guard_msgs in
-- example : 3 ≤ 5 := by
--   #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
--   sorry
