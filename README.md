# LeanSearchClient

LeanSearchClient provides syntax for search using the [leansearch API](https://leansearch.net/) and the [LeanStateSearch](https://premise-search.com) API from within Lean. It allows you to search for Lean tactics and theorems using natural language. It also allows searches on [Loogle](https://loogle.lean-lang.org/json) from within Lean.

We provide syntax to make a query and generate `TryThis` options to click or use a code action to use the results. The queries are of four forms:

* `Command` syntax: `#search "search query"` as a command.
* `Term` syntax: `#search "search query"` as a term.
* `Tactic` syntax: `#search "search query"` as a tactic.
* `Tactic` syntax based on state: `#search`.

In all cases results are displayed in the Lean Infoview and clicking these replaces the query text. In the cases of a query for tactics only valid tactics are displayed.

Which backend is used is determined by the `leansearchclient.backend` option.

## Examples

The following are examples of using the leansearch API. The search is triggered when the sentence ends with a full stop (period) or a question mark.

### Query Command

The common command for all backends:

```lean
#search "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

We also have commands for specific backend:

```lean
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

### Query Term

The general command:

```lean
example := #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
```


For `leansearch`:

```lean
example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

### Query Tactic

Note that only valid tactics are displayed.

The general command has two variants. With a string, calling LeanSearch:

```lean
example : 3 ≤ 5 := by
  #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

Without a string, calling LeanStateSearch

```lean
example : 3 ≤ 5 := by
  #search
  sorry
```

There are also specific commands for the different backends.

For `leansearch`:

```lean
example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

For LeanStateSearch:

```lean
example : 3 ≤ 5 := by
  #statesearch
  sorry
```


## Loogle Search

The `#loogle` command can also be used in all three modes. The syntax in this case is `#loogle <search query>` as in the following examples.

```lean
#loogle List ?a → ?a

example := #loogle List ?a → ?a

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry
```