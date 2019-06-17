import .tab

open tactic 
variable {p : Prop}

example : p := 
by do proof_by_contradiction

#exit

#check @classical.by_contradiction

example : p := 
by do refine ``(classical.by_contradiction _),
      -- trace "After refine : ", trace_state,
      intro `_,
      -- trace "After intro : ", trace_state,
      skip