import data.polynomial

open polynomial

universe u

-- Doesn't work
variables {γ : Type u} [integral_domain γ] [decidable_eq γ] [comm_semiring γ]
lemma test {a : polynomial γ} (ha : is_unit a) : degree a = 0 := degree_eq_zero_of_is_unit ha

-- Works
variables {α : Type u} [integral_domain α] [decidable_eq α]
lemma test' {a : polynomial α} (ha : is_unit a) : degree a = 0 := degree_eq_zero_of_is_unit ha

