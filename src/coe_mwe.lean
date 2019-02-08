import data.polynomial
import tactic.squeeze

open polynomial

set_option pp.all true

universe u 

local attribute [instance, priority 0] classical.prop_decidable

variables {α : Type u} {a: α} 
variables [integral_domain α] {p q r s : polynomial α}
variable [decidable_eq α]

lemma deg_c_times_x_to_n_eq_n (n : ℕ) {c : α} (hc : c ≠ 0) : degree (C c * X^n) = n := 
have h1: leading_coeff (C c) * leading_coeff X^n ≠ 0, by simp [hc], 
show degree (C c * X^n) = n, from calc
        degree (C c * X^n) = degree (C c) + degree (X^n) : by rw [degree_mul_eq]
                    ... = 0 + degree (X^n) : by rw [degree_C hc]
                    ... = 0 + n : by rw [degree_X_pow] -- simp [degree_X_pow] also works fine. 
                    ... = n : by simp

lemma minimal (n : ℕ) : degree (X^n : polynomial α) = n := by squeeze_simp 

lemma step_by_step (n : ℕ) : degree (X^n : polynomial α) = n := 
begin 
   rw polynomial.degree_pow_eq,
   rw polynomial.degree_X,
   rw add_monoid.smul_one
end 

lemma minimal' (n : ℕ) : add_monoid.smul n 1 = ↑n := by simp -- works 

lemma minimal'' (n : ℕ) : add_monoid.smul n (degree X) = ↑n := by simp