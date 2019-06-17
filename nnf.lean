
import .tab

variables {p q r s : Prop}

open tactic

#exit 

#check imp_iff_not_or

/- simp -/
example : p → q := 
by simp only [ imp_iff_not_or ] 

/- simp hypothesis -/
example (h : p → q) : false := 
by simp only [ imp_iff_not_or ] -- at h

/- simp everywhere -/
example (h1 : p → q) (h2 : ¬ (q ∨ r)) : false := 
by simp only [ imp_iff_not_or, not_or_distrib ] at h1 -- at *

/- simp subformula -/
example (h : p ∧ ¬ (q ∨ r)) : false := 
by simp only [ not_or_distrib ] at *

/- simp repeatedly -/
example (h : p → (q → r)) : false := 
by simp only [ imp_iff_not_or ] at *

example (h1 : ¬ ((p → q) → r)) (h2 : p ∧ ¬ q) : false := 
by normalize
