import data.polynomial

open polynomial

universe u

variables {α : Type u} [integral_domain α] [decidable_eq α]

lemma minimal_example (n : ℕ) : degree (X^n : polynomial α) = n :=
begin
  simp,
  -- We're left with `↑n = ↑n`
  sorry
end

-- Turning on `set_option pp.all true` we can see the actual goal, and provide a lemma:

lemma nat.cast_with_bot (n : ℕ) : @eq.{1} (with_bot.{0} nat)
    (@coe.{1 1} nat (with_bot.{0} nat)
       (@coe_to_lift.{1 1} nat (with_bot.{0} nat)
          (@coe_base.{1 1} nat (with_bot.{0} nat)
             (@nat.cast_coe.{0} (with_bot.{0} nat)
                (@add_monoid.to_has_zero.{0} (with_bot.{0} nat) (@with_bot.add_monoid.{0} nat nat.add_monoid))
                (@with_bot.has_one.{0} nat nat.has_one)
                (@add_semigroup.to_has_add.{0} (with_bot.{0} nat)
                   (@add_monoid.to_add_semigroup.{0} (with_bot.{0} nat)
                      (@with_bot.add_monoid.{0} nat nat.add_monoid))))))
       n)
    (@coe.{1 1} nat (with_bot.{0} nat) (@coe_to_lift.{1 1} nat (with_bot.{0} nat) (@with_bot.has_coe_t.{0} nat)) n) :=
begin
  unfold_coes,
  induction n,
  { simp, refl },
  { dsimp [nat.cast],
    rw n_ih,
    refl }
end

-- But surely there is something more general we're meant to do here?!

-- This problem originally came up when we started to refactor the following proof:
lemma deg_c_times_x_to_n_eq_n (n : ℕ) {c : α} (hc : c ≠ 0) : degree (C c * X^n) = n :=
by calc
        degree (C c * X^n) = degree (C c) + degree (X^n) : by rw [degree_mul_eq]
                    ... = 0 + degree (X^n) : by rw [degree_C hc]
                    ... = 0 + n : by rw [degree_X_pow]
                    ... = n : by simp

-- All the rewrites should be achievable via `simp`, but we run into the mismatched coercions:
lemma deg_c_times_x_to_n_eq_n' (n : ℕ) {c : α} (hc : c ≠ 0) : degree (C c * X^n) = n :=
by calc
        degree (C c * X^n) = degree (C c) + degree (X^n) : by rw [degree_mul_eq]
                    ... = 0 + degree (X^n) : by rw [degree_C hc]
                    ... = 0 + n : by simp
                    ... = n : by simp

-- Making `nat.cast_with_bot` above into a simp lemma solves the problem:
attribute [simp] nat.cast_with_bot

lemma deg_c_times_x_to_n_eq_n''' (n : ℕ) {c : α} (hc : c ≠ 0) : degree (C c * X^n) = n :=
by simp [degree_C hc]

