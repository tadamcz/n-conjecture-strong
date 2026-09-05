import StrongFour

-- These conclusions mention only four integers and contain no conjectural premise.
#check StrongFour.no_uniform_bound
#check StrongFour.qualityLimsup_ge
#print axioms StrongFour.family_admissible
#print axioms StrongFour.no_uniform_bound
#print axioms StrongFour.conjecture_false
#print axioms StrongFour.qualityLimsup_ge
#print axioms StrongFour.qualityLimsup_ne_one

example : ¬ StrongFour.Conjecture := StrongFour.conjecture_false
example : ((9 / 8 : ℝ) : EReal) ≤ StrongFour.qualityLimsup := StrongFour.qualityLimsup_ge
