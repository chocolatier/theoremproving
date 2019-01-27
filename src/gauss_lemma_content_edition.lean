import data.polynomial
import algebra.gcd_domain
import order.bounded_lattice

open polynomial
open classical

local attribute [instance, priority 0] classical.prop_decidable

universe u 

variables {α : Type u} {a: α} 

variables [integral_domain α] {p q r s : polynomial α}
variable [decidable_eq α]
variable [gcd_domain α]

