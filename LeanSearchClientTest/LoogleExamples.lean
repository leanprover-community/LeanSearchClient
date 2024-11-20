import LeanSearchClient.LoogleSyntax

/-!
# Loogle Examples

Examples of using the Loogle API. The search is triggered by the word at the end of the query.
-/

-- #loogle List ?a → ?a

-- example := #loogle List ?a → ?a


-- set_option loogle.queries 1

-- example : 3 ≤ 5 := by
--   #loogle Nat.succ_le_succ
--   sorry

-- example : 3 ≤ 5 := by
--   #loogle
--   decide

/-!
More examples to test comments do not interfere with the search or caching.
-/

#loogle ?a * _ < ?a * _ ↔ _
#loogle ?a * _ < ?a * _ ↔ _ /- foo -/
#loogle ?a * _ < ?a * _ ↔ _


-- comment
#loogle ?a * _ < ?a * _ ↔ _

/--
info: Loogle Search Results
• #check Option.get!
-/
#guard_msgs in
  #loogle Option ?a → ?a, "get!"

/- hello -/
