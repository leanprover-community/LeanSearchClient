import LeanSearchClient.Syntax

set_premise_selector LeanSearchClient.leanStateSearchSelector

-- This should return something containing `add_comm` and/or `Nat.add_comm`,
-- but we don't have an easy way to verify this.
example (a b : Nat) : a + b = b + a := by
  suggest_premises
  grind
