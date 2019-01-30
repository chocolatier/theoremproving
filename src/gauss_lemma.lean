import data.polynomial
import ring_theory.unique_factorization_domain
import order.bounded_lattice
import ring_theory.localization
import data.set
import data.nat.basic


open polynomial
open classical
open localization
open set
open nat

local attribute [instance, priority 0] classical.prop_decidable

universe u 

variables {α : Type u} {a: α} 

variables [integral_domain α] {p q r s : polynomial α}
variable [decidable_eq α]
variable [unique_factorization_domain α]
variable [has_mod α]

def is_const (p : polynomial α) : Prop := nat_degree p = 0 

instance is_const.decidable : decidable (is_const p) :=
by unfold is_const; apply_instance

def leading_coeff_non_unit (p : polynomial α) : Prop := ¬is_unit (leading_coeff p) 

instance is_unit.decidable : decidable (is_unit a) := sorry

instance leading_coeff_non_unit.decidable : decidable (leading_coeff_non_unit p) :=
by unfold leading_coeff_non_unit; apply_instance

def non_unit_const (p : polynomial α) : Prop := (is_const p) ∧ (leading_coeff_non_unit p)

instance non_unit_const.decidable : decidable (non_unit_const p) :=
by unfold non_unit_const; apply_instance

lemma not_const_imp_non_zero  : ¬is_const p → p ≠ (0 : polynomial α) := 
mt begin 
 intro hp,
 show is_const p, by {rw [hp, is_const], simp}
end

lemma deg_c_times_x_to_n_eq_n (n : ℕ) {c : α} (hc : c ≠ 0) : degree (C c * X^n) = n := 
have h1: leading_coeff (C c) * leading_coeff X^n ≠ 0, by simp [hc], 
show degree (C c * X^n) = n, from calc
        degree (C c * X^n) = degree (C c) + degree (X^n) : by rw [degree_mul_eq]
                    ... = 0 + degree (X^n) : by rw [degree_C hc]
                    ... = 0 + n : by rw degree_X_pow 
                    ... = n : by simp


lemma nat_deg_zero_lt_nat_deg_p (hp : ¬is_const p) {q : polynomial α} (hq : q = 0) : nat_degree q < nat_degree p :=
begin 
    have h1 : nat_degree q = 0, by {rw hq, exact nat_degree_zero},
    have h2 : nat_degree p ≠ 0, by exact hp,
    rw h1, 
    show 0 < nat_degree p, by exact nat.pos_iff_ne_zero'.2 h2 
end 

lemma nat_deg_non_zero_lt_nat_deg_p  {p q : polynomial α} (ha : degree q < degree p) (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree q < nat_degree p := 
begin 
    have h1 : ↑(nat_degree q) < ↑(nat_degree p), by {rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq] at ha, exact ha},
    show nat_degree q < nat_degree p, by{rw with_bot.coe_lt_coe at h1, exact h1}
end 

lemma const_mod_decreasing (hp: ¬is_const p) :
    nat_degree (p - C (leading_coeff p) * X^(nat_degree p)) < nat_degree p := 
begin
    have h1 : p ≠ 0, by exact not_const_imp_non_zero hp, 
    have h2 : (leading_coeff p) = leading_coeff  (C (leading_coeff p) * X^(nat_degree p)), by simp,
    have h5 : leading_coeff p ≠ 0, by exact mt leading_coeff_eq_zero.1 h1,
    have h3 : (degree p) = (degree (C (leading_coeff p) * X^(nat_degree p))), by rw [deg_c_times_x_to_n_eq_n (nat_degree p) h5, degree_eq_nat_degree h1],
    have h4 : _ := degree_sub_lt h3 h1 h2,  
    cases em (p - C (leading_coeff p) * X ^ nat_degree p = 0) with heq0 hneq0,
        by exact nat_deg_zero_lt_nat_deg_p hp heq0,
        by exact nat_deg_non_zero_lt_nat_deg_p h4 h1 hneq0
end 

def mod_by_const : Π (p : polynomial α) {q : polynomial α},
  is_const q → polynomial α
| p := λ q hq,
    let
        z := C ((leading_coeff p) % (leading_coeff q)) * X^(nat_degree p),
        rem := p - C (leading_coeff p) * X^(nat_degree p)
            in
                if hp: ¬is_const p then
                    have wf : _ := const_mod_decreasing hp, 
                    z + (mod_by_const rem hq)
                else
                    z
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf nat_degree⟩]}

-- pulls out the is_const and applies mod.
def mod_by_non_unit_const : Π (p : polynomial α) {q : polynomial α},
  non_unit_const q → polynomial α
| p := λ q hq,
    have hc : is_const q := and.left hq,
    mod_by_const p hc

def const_divisor : Π (p : polynomial α) {q : polynomial α}, is_const q → Prop 
| p q := λ hq,
    mod_by_const p hq = 0

-- Maybe better off using GCD coefft = 1? Have UFD α so can produce GCD Domain α...
def primitive (p : polynomial α) : Prop := ∀(q : polynomial α) (hq: non_unit_const q), (mod_by_non_unit_const p hq ≠ 0)

lemma h_div_lemma {p : polynomial α} (hp : ¬primitive p) : ∃(m : polynomial α) (hm : non_unit_const m), mod_by_non_unit_const p hm = 0 := 
begin 
    sorry
end

lemma irred_div_pq_imp_irred_div_p_or_irred_div_q (p q : polynomial α) (irreducible n : polynomial α) (hc : non_unit_const n) (hdiv : mod_by_non_unit_const (p*q) hc = 0): 
    const_divisor p (and.left hc) ∨ const_divisor q (and.left hc) := sorry

lemma non_unit_const_divisor_imp_non_primitive (p : polynomial α) {q : polynomial α} (hq : non_unit_const q) : const_divisor p (and.left hq) → ¬primitive p := sorry

lemma prod_of_prim_is_prim (p q : polynomial α) : (primitive p ∧ primitive q) → primitive (p * q) := 
begin 
    intros h_p_q, 
    by_contradiction h_pq, 
    have hp : primitive p := and.left h_p_q,
    have hq : primitive q := and.right h_p_q,
    have h_div : ∃(m : polynomial α) (hm : non_unit_const m), mod_by_non_unit_const (p * q) hm = 0, exact (h_div_lemma h_pq), 
    have h_irred_div : ∃(n : polynomial α) (hn : (non_unit_const n) ∧ (irreducible n)), mod_by_non_unit_const (p * q) (and.left hn) = 0, by sorry, 
    have h_npq : ¬primitive p ∨ ¬primitive q, by sorry,
    show false,
         cases h_npq,
            contradiction,
            contradiction
end
