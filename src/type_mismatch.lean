import data.polynomial

open polynomial

universe u

-- Doesn't work
variables {γ : Type u} [I : integral_domain γ] [D : decidable_eq γ] [comm_semiring γ]
lemma test {a : polynomial γ} (ha : is_unit a) : degree a = 0 := @degree_eq_zero_of_is_unit γ I D a ha

-- Works
variables {α : Type u} [integral_domain α] [decidable_eq α]
lemma test' {a : polynomial α} (ha : is_unit a) : degree a = 0 := degree_eq_zero_of_is_unit ha

