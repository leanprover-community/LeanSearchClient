import LeanSearchClient.LoogleSyntax

/-!
# Loogle Examples

Examples of using the Loogle API. The search is triggered by the word do_search at the end of the query.
-/

#loogle List ?a → ?a do_search

example := #loogle List ?a → ?a do_search


set_option loogle.queries 1

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ do_search
  sorry
