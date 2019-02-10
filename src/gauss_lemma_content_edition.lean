import data.polynomial
import algebra.gcd_domain
import ring_theory.ideals
import ring_theory.ideal_operations
import ring_theory.localization

open polynomial
open classical
open ideal
open localization

local attribute [instance, priority 0] classical.prop_decidable

universe u

variables {α : Type u} {a: α}

variable [decidable_eq α]
variable [gcd_domain α]
variables [integral_domain α] {p q r s : polynomial α}
variable [has_one α] -- Exclude the trivial ring

def is_const (p : polynomial α) : Prop := nat_degree p = 0 

def content (p : polynomial α) : ideal α :=
let
    supp := p.support,
    coeffts := (supp.image p.to_fun).to_set
in
    span coeffts

def is_primitive (p : polynomial α) : Prop :=
content p = span (singleton (1 : α))

def polynomial_coeff_gcd (p : polynomial α) : α := sorry

-- noncomputable def ideal_gcd (i : ideal α) : (ideal α) := some (λx:ideal α, i ≤ x ∧ (∀(j : ideal α), i ≤ j → x ≤ j))

lemma cont_prod_sub_prod_cont {p q : polynomial α} (x : α) (hx : x ∈ content (p * q)) : (x ∈ content p * content q) := sorry

lemma cont_scalar_mul_fwd (x : α) {p : polynomial α} {a : α} (hx : x ∈ content (C a * p)) : (x ∈ (span (singleton a)) * (content p)) := sorry

lemma cont_scalar_mul (p : polynomial α) (a : α) : (content (C a * p)) = ((span (singleton a)) * (content p)) := sorry

-- lemma cont_gcd_eq (p : polynomial α) (q : polynomial α) : ideal_gcd (content (p * q)) = ideal_gcd (content p) * ideal_gcd (content q) := sorry

lemma prod_prim_is_prim {p q : polynomial α} (hp: is_primitive p) (hq : is_primitive q)  : is_primitive (p * q) := sorry

def to_quot (a : α) : quotient_ring α := sorry -- ↑a

def quot_poly (p : polynomial α) : polynomial (quotient_ring α) := to_quot ∘ p 

lemma irred_imp_gcd_coeff_1 (p : polynomial α) (hp : irreducible p) : polynomial_coeff_gcd p = 1 := sorry

lemma irred_in_base_imp_irred_in_quot {p : polynomial α} (hp_p : is_primitive p) (hp_ir : irreducible p) (hp_nc : ¬is_const p) : irreducible (quot_poly p) := 
begin 
  sorry
end

-- lemma irred_in_quot_imp_irred_in_base {p : polynomial (quotient_ring α)} (hp_ir : irreducible p) 