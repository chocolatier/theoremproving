import data.polynomial
import ring_theory.unique_factorization_domain

open polynomial
open classical

universe u 

variables {α : Type u} {a: α} 

variables [integral_domain α] {p q r s : polynomial α}
variable [decidable_eq α]
variable [unique_factorization_domain α]
variable [has_mod α]

-- -- 
-- theorem has_R_root_imp_has_frac_R_root (p : polynomial α) : (p = p) := sorry

-- def has_non_unit_divisor (a : α) : Prop := ∃(b : α), (¬is_unit b) ∧ (b ∣ a)

-- lemma non_unit_div_ab_imp_non_unit_div_a_or_non_unit_div_b (a b : α) : ∃(c : α), 
--     (¬is_unit c) ∧ (c ∣ (a * b)) → (has_non_unit_divisor a) ∨ (has_non_unit_divisor b) := sorry

-- def primitive (p : polynomial α) : Prop :=
-- ¬(∃(a : α), ∃(r : polynomial α), (¬is_unit a) ∧ p = (C a) * r)

def is_const (p : polynomial α) : Prop := nat_degree p = 0 

instance is_const.decidable : decidable (is_const p) :=
by unfold is_const; apply_instance

def leading_coeff_non_unit (p : polynomial α) : Prop := ¬is_unit (leading_coeff p) 

def non_unit_const (p : polynomial α) : Prop := (is_const p) ∧ (leading_coeff_non_unit p)

lemma const_mod_decreasing (hp: ¬is_const p) (h: is_const q) :
    nat_degree (p - C (leading_coeff p) * X^(nat_degree p)) < nat_degree p := sorry

def mod_by_const : Π (p : polynomial α) {q : polynomial α},
  is_const q → polynomial α
| p := λ q hq,
    let
        z := C ((leading_coeff p) % (leading_coeff q)) * X^(nat_degree p),
        rem := p - C (leading_coeff p) * X^(nat_degree p)
            in
                if hp: ¬is_const p then
                    have wf : _ := const_mod_decreasing hp hq, 
                    z + (mod_by_const rem hq)
                else
                    z
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf nat_degree⟩]}

-- pulls out the is_const and applies mod.
def mod_by_non_unit_const : Π (p : polynomial α) {q : polynomial α},
  non_unit_const q → polynomial α
| p := λ q hq,
    have hc : is_const q := and.left hq,
    mod_by_const p hc


