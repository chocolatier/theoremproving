import data.polynomial

open polynomial

universe u

variables {γ : Type u} [comm_semiring γ] [decidable_eq γ] [integral_domain γ]
lemma test {a : polynomial γ} (ha : is_unit a) : degree a = 0 := degree_eq_zero_of_is_unit ha

variables {α : Type u} [integral_domain α] [decidable_eq α]
lemma test' {a : polynomial α} (ha : is_unit a) : degree a = 0 := degree_eq_zero_of_is_unit ha

