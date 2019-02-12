import data.polynomial
import algebra.gcd_domain
import ring_theory.ideals
import ring_theory.ideal_operations
import ring_theory.localization

open polynomial
open classical
open ideal
open localization

noncomputable theory

-- set_option trace.class_instances true
-- set_option class.instance_max_depth 1000

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

lemma cont_prod_sub_prod_cont {p q : polynomial α} (x : α) (hx : x ∈ content (p * q)) : (x ∈ content p * content q) := sorry

lemma cont_scalar_mul_fwd (x : α) {p : polynomial α} {a : α} (hx : x ∈ content (C a * p)) : (x ∈ (span (singleton a)) * (content p)) := 
begin 
    unfold content at hx,
    unfold content,
    unfold has_mul.mul,
    unfold has_mul.mul at hx,
end

lemma cont_scalar_mul (p : polynomial α) (a : α) : (content (C a * p)) = ((span (singleton a)) * (content p)) := sorry

lemma prod_cont_sub_rad (p q : polynomial α) : content p * content q ≤ radical (content (p * q)) := sorry

lemma prod_prim_is_prim {p q : polynomial α} (hp: is_primitive p) (hq : is_primitive q)  : is_primitive (p * q) := sorry

def to_quot (a : α) : quotient_ring α := ⟦(a, (1 : non_zero_divisors α))⟧

def quot_poly (p : polynomial α) : polynomial (quotient_ring α) := p.map to_quot

lemma irred_imp_gcd_coeff_1 (p : polynomial α) (hp : irreducible p) : polynomial_coeff_gcd p = 1 := sorry

lemma quot_poly_mult (p : polynomial (quotient_ring α)) : ∃(c : α) (d : polynomial α), quot_poly (C c) * p = quot_poly d := sorry 

lemma irred_in_base_imp_irred_in_quot {p : polynomial α} (hp_p : is_primitive p) (hp_ir : irreducible p) (hp_nc : ¬is_const p) : irreducible (quot_poly p) := 
begin 
    let p' := quot_poly p,
    by_contradiction h_contr,
    have h1: ∃(m n : polynomial (quotient_ring α)), (¬ is_unit m) ∧ (¬ is_unit n) ∧ m * n = p', by sorry,
    apply exists.elim h1,
    intros m hm,
    apply exists.elim hm,
    intros n h_prod, -- ideally both apply and intros should be a single statement
    have h2: ∃ (c : α) (d : polynomial α), quot_poly (C c) * m = quot_poly d, by exact quot_poly_mult m, 
    apply exists.elim h2,
    intros c hc,
    apply exists.elim hc,
    intros d hd,
    have h3: ∃(c₂ : α) (d₂ : polynomial α), quot_poly (C c₂) * n = quot_poly d₂, by exact quot_poly_mult n, 
    apply exists.elim h3,
    intros c₂ hc₂,
    apply exists.elim hc₂,
    intros d₂ hd₂,

end

-- lemma irred_in_quot_imp_irred_in_base {p : polynomial (quotient_ring α)} (hp_ir : irreducible p) 