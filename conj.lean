import .tab

variables {p q r s : Prop}

open tactic

example (h : p ∧ q) : false := by split_conj

-- meta def find_conj' : list expr → tactic expr
-- | []        := failed
-- | (e :: es) := do trace "expr : ", trace e,
--                   t ← infer_type e,
--                   trace "expr type : ", trace t,
--                   match t with
--                   | `(%%a ∧ %%b) := trace "conjunction" >> return e
--                   | _            := trace "not a conjunction" >> find_conj' es
--                   end

#exit

example (h : p ∧ q) : false :=
by do l ← local_context,
      -- trace l,
      e ← find_conj l,
      -- trace e,
      cases e,
      -- trace "After cases : ", trace_state,
      skip

example (h1 : p ∧ q) (h2 : r ∧ s) : false := by split_conjs

example (h1 : p ∧ q) (h2 : r ∧ s) : false := by split conj --repeat {split_conj}