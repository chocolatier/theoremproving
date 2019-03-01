import data.polynomial
import ring_theory.localization

open polynomial

local attribute [instance, priority 0] classical.prop_decidable

section
variables {α : Type} [comm_ring α] 
lemma works {p : polynomial α} {r : α} : ideal.quotient.mk (ideal.span (singleton (C r))) p = 0 := sorry
end

section
set_option trace.class_instances true

variables {α : Type} [integral_domain α] 
lemma timeout {p : polynomial α} {r : α} : ideal.quotient.mk (ideal.span (singleton (C r))) p = 0 := sorry
end