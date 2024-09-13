# LeanSearchClient

LeanSearchClient provides syntax for search using the [leansearch API](https://leansearch.net/) from within Lean. It allows you to search for Lean tactics and theorems using natural language.

We provide syntax to make a query and generate `TryThis` options to click or use a code action to use the results. The queries are of three forms:

* `Command` syntax: `#leansearch "search query"` as a command.
* `Term` syntax: `#leansearch "search query"` as a term.
* `Tactic` syntax: `#leansearch "search query"` as a tactic.

In all cases results are displayed in the Lean Infoview and clicking these replaces the query text. In the cases of a query for tactics only valid tactics are displayed.

## Examples

The following are examples of using the leansearch API. The search is triggered when the sentence ends with a full stop (period) or a question mark.

### Query Command

For `leansearch`:

```lean
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

For `moogle`:

```lean
#moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
```


### Query Term

For `leansearch`:

```lean
example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

For `moogle`:

```lean
example := #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
```


### Query Tactic

Note that only valid tactics are displayed.

For `leansearch`:

```lean
example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

For `moogle`:

```lean
example : 3 ≤ 5 := by
  #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```
