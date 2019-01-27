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

variables [integral_domain α] {p q r s : polynomial α}
variable [decidable_eq α]
variable [comm_ring α]
variable [gcd_domain α]
variable [has_one α] -- Exclude the trivial ring

/-gauss_lemma_content_edition.lean:20:0: error
synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  no_zero_divisors.to_has_zero α
inferred
  mul_zero_class.to_has_zero α
-/

def content (p : polynomial α) : ideal α :=  sorry
-- let 
--     coeffts := p.support.map p.to_fun 
-- in 
--     span coeffts

def is_primitive (p : polynomial α) : Prop := 
content p = span (singleton (1 : α))
  
lemma cont_mul_hom (p : polynomial α) (a : α) : (content (C a * p)) = ((span (singleton a)) * (content p)) := sorry 

#check gcd (span (singleton α)) 

lemma prod_prim_is_prim {p q : polynomial α} (hp: is_primitive p) (hq : is_primitive q)  : is_primitive (p * q) := sorry

