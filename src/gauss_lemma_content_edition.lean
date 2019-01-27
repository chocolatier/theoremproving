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

def content (p : polynomial α) : ideal α := 
let 
    coeffts := map p.to_fun p.support
in 
    span coeffts
  