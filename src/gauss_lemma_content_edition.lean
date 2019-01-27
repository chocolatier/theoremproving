import data.polynomial
import algebra.gcd_domain
import ring_theory.ideals

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

/-gauss_lemma_content_edition.lean:20:0: error
synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  no_zero_divisors.to_has_zero α
inferred
  mul_zero_class.to_has_zero α
-/

def content (p : polynomial α) : ideal α := 
let 
    coeffts := p.support.map p.to_fun 
in 
    span coeffts
  