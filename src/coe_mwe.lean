import data.polynomial
import tactic.squeeze

open polynomial

set_option pp.all true

universe u 

variables {α : Type u} 
variable [decidable_eq α]
variables [integral_domain α]

lemma minimal (n : ℕ) : degree (X^n : polynomial α) = n := by simp 

lemma working (n : ℕ) : degree (X^n : polynomial α) = n := by simp [degree_X_pow] -- this works

lemma step_by_step (n : ℕ) : degree (X^n : polynomial α) = n := 
begin 
   rw polynomial.degree_pow_eq,
   rw polynomial.degree_X,
   rw add_monoid.smul_one
end 

-- Source of error
lemma deg_c_times_x_to_n_eq_n (n : ℕ) {c : α} (hc : c ≠ 0) : degree (C c * X^n) = n := 
show degree (C c * X^n) = n, from calc
        degree (C c * X^n) = degree (C c) + degree (X^n) : by rw [degree_mul_eq]
                    ... = 0 + degree (X^n) : by rw [degree_C hc]
                    ... = 0 + n : by rw [degree_X_pow] -- simp [degree_X_pow] also works fine. 
                    ... = n : by simp
