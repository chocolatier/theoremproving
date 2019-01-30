import data.polynomial
import algebra.gcd_domain
import ring_theory.ideals
import ring_theory.ideal_operations

open polynomial
open classical
open ideal

local attribute [instance, priority 0] classical.prop_decidable

universe u

variables {α : Type u} {a: α}

variable [decidable_eq α]
variable [gcd_domain α]
variables [integral_domain α] {p q r s : polynomial α}
variable [has_one α] -- Exclude the trivial ring

def content (p : polynomial α) : ideal α :=
let
    supp := p.support,
    coeffts := (supp.image p.to_fun).to_set
in
    span coeffts

def is_primitive (p : polynomial α) : Prop :=
content p = span (singleton (1 : α))

lemma cont_mul_hom_sub {p q : polynomial α} (x : α) (hx : x ∈ content (p * q)) : (x ∈ content p * content q) := sorry

lemma cont_scalar_mul_fwd (x : α) {p : polynomial α} {a : α} (hx : x ∈ content (C a * p)) : (x ∈ (span (singleton a)) * (content p)) := sorry

lemma cont_scalar_mul (p : polynomial α) (a : α) : (content (C a * p)) = ((span (singleton a)) * (content p)) := sorry

#check gcd (span (singleton α))

lemma prod_prim_is_prim {p q : polynomial α} (hp: is_primitive p) (hq : is_primitive q)  : is_primitive (p * q) := sorry

