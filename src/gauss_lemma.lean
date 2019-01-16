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

local attribute [instance] prop_decidable

def is_const (p : polynomial α) : Prop := nat_degree p = 0 

-- instance is_const.decidable : decidable (is_const p) :=
-- by unfold is_const; apply_instance

def leading_coeff_non_unit (p : polynomial α) : Prop := ¬is_unit (leading_coeff p) 

-- instance is_unit.decidable : decidable (is_unit a) := sorry

-- instance leading_coeff_non_unit.decidable : decidable (leading_coeff_non_unit p) :=
-- by unfold leading_coeff_non_unit; apply_instance

def non_unit_const (p : polynomial α) : Prop := (is_const p) ∧ (leading_coeff_non_unit p)

-- instance non_unit_const.decidable : decidable (non_unit_const p) :=
-- by unfold non_unit_const; apply_instance


lemma const_mod_decreasing (hp: ¬is_const p) :
    nat_degree (p - C (leading_coeff p) * X^(nat_degree p)) < nat_degree p := 
    have h1 : p ≠ 0, by sorry, 
    have h2 : (leading_coeff p) = leading_coeff  (C (leading_coeff p) * X^(nat_degree p)), by simp,
    have h3 : (degree p) = (degree (C (leading_coeff p) * X^(nat_degree p))), by sorry,
    have h4 : _ := degree_sub_lt h3 h1 h2,    
    by sorry

def mod_by_const : Π (p : polynomial α) {q : polynomial α},
  is_const q → polynomial α
| p := λ q hq,
    let
        z := C ((leading_coeff p) % (leading_coeff q)) * X^(nat_degree p),
        rem := p - C (leading_coeff p) * X^(nat_degree p)
            in
                if hp: ¬is_const p then
                    have wf : _ := const_mod_decreasing hp, 
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

def const_divisor : Π (p : polynomial α) {q : polynomial α}, is_const q → Prop 
| p q := λ hq,
    mod_by_const p hq = 0

-- Maybe better off using GCD coefft = 1? Have UFD α so can produce GCD Domain α...
def primitive (p : polynomial α) : Prop := ∀(q : polynomial α) (hq: non_unit_const q), (mod_by_non_unit_const p hq ≠ 0)

-- instance primitive.decidable : decidable (primitive p) := sorry

lemma h_div_lemma {p : polynomial α} (hp : ¬primitive p) : ∃(m : polynomial α) (hm : non_unit_const m), mod_by_non_unit_const p hm = 0 := sorry

lemma irred_div_pq_imp_irred_div_p_or_irred_div_q (p q : polynomial α) (irreducible n : polynomial α) (hc : non_unit_const n): 
    const_divisor p (and.left hc) ∨ const_divisor q (and.left hc) := sorry

lemma non_unit_const_divisor_imp_non_primitive (p : polynomial α) {q : polynomial α} (hq : non_unit_const q) : const_divisor p (and.left hq) → ¬primitive p := sorry

lemma prod_of_prim_is_prim (p q : polynomial α) : (primitive p ∧ primitive q) → primitive (p * q) := 
begin 
    intros h_p_q, 
    by_contradiction h_pq, 
    have hp : primitive p := and.left h_p_q,
    have hq : primitive q := and.right h_p_q,
    have h_div : ∃(m : polynomial α) (hm : non_unit_const m), mod_by_non_unit_const (p * q) hm = 0, exact (h_div_lemma h_pq), 
    have h_irred_div : ∃(n : polynomial α) (hn : non_unit_const n) (irreducible n), mod_by_non_unit_const (p * q) hn = 0, by sorry, 
    have h_npq : ¬primitive p ∨ ¬primitive q, by sorry,
    -- Or elim stuff here
end
