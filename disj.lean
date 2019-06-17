import .tab

variables {p q r s : Prop}

open tactic

example (h : p ∨ q) : false := by split_disj

-- meta def find_disj' : list expr → tactic expr
-- | []        := failed
-- | (e :: es) := do trace "expr : ", trace e,
--                   t ← infer_type e,
--                   trace "expr type : ", trace t,
--                   match t with
--                   | `(%%a ∨ %%b) := trace "disjunction" >> return e
--                   | _            := trace "not a disjunction" >> find_disj' es
--                   end

#exit 

example (h : p ∨ q) : false :=
by do l ← local_context,
      -- trace l,
      e ← find_disj l,
      -- trace e,
      cases e,
      -- trace "After cases : ", trace_state,
      skip