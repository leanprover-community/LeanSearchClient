import LeanSearchClient.LoogleSyntax

/-!
# Loogle Examples

Examples of using the Loogle API. The search is triggered by the word at the end of the query.
-/

#loogle List ?a → ?a

example := #loogle List ?a → ?a


set_option loogle.queries 1

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry

#loogle List ?a → ?b
