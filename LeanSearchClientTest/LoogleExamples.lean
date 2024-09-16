import LeanSearchClient.LoogleSyntax

/-!
# Loogle Examples

Examples of using the Loogle API. The search is triggered by the word go at the end of the query.
-/

#loogle List ?a → ?a go

example := #loogle List ?a → ?a go


set_option loogle.queries 1

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ go
  sorry
