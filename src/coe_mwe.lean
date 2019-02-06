import data.polynomial

open polynomial

universe u 

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

lemma minimal (n : ℕ) : degree (X^n : polynomial α) = n := by simp