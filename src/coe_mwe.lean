import data.polynomial
import tactic.squeeze

open polynomial

universe u

variables {α : Type u} [integral_domain α] [decidable_eq α]

lemma minimal_example (n : ℕ) : degree (X^n : polynomial α) = n :=
begin
  simp,
  -- We're left with `↑n = ↑n`
  sorry
end

@[simp] lemma nat.cast_with_bot_cast {α} [add_monoid α] [has_one α] : ∀ n : ℕ,
  (n : with_bot α) = (n : α)
| 0 := rfl
| (n+1) := by simp [nat.cast_with_bot_cast n]

@[simp] lemma nat.cast_with_bot : ∀ n : ℕ,
  @coe _ (with_bot ℕ) (@coe_to_lift _ _ (@coe_base _ _ nat.cast_coe)) n = n :=
by simp

lemma minimal_example' (n : ℕ) : degree (X^n : polynomial α) = n :=
by simp

-- Maybe this lemma won't even be needed; just use the simplifier in its place.
lemma deg_c_times_x_to_n_eq_n (n : ℕ) {c : α} (hc : c ≠ 0) : degree (C c * X^n) = n :=
by simp *

