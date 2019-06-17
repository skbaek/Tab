import .tab

variables {p q r s : Prop}

open tactic

-- example (h1 : ¬ ((p → q) → r)) (h2 : p ∧ ¬ q) : r := by tab
-- 
-- example (h1 : ¬ ((p → q) → r)) (h2 : p ∧ ¬ q) : r := 
-- by do proof_by_contradiction,
--       -- trace "After pbc : ", trace_state,
--       normalize,
--       -- trace "After normalization : ", trace_state,
--       tab_aux,
--       skip
-- 
-- meta def tab_aux : tactic unit :=
-- do split_conjs,
--    contradiction <|>
--      (split_disj >> tab_aux >> tab_aux)