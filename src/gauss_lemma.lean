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

-- set_option pp.all true

def is_const (p : polynomial α) : Prop := nat_degree p = 0 

instance is_const.decidable : decidable (is_const p) :=
by unfold is_const; apply_instance

def leading_coeff_non_unit (p : polynomial α) : Prop := ¬is_unit (leading_coeff p) 

def non_unit_const (p : polynomial α) : Prop := (is_const p) ∧ (leading_coeff_non_unit p)

lemma not_const_imp_non_zero  : ¬is_const p → p ≠ (0 : polynomial α) := 
mt begin 
 intro hp,
 show is_const p, by {rw [hp, is_const], simp}
end

def const_divisor : Π (p q : polynomial α),  Prop 
| p q := is_const q ∧ q ∣ p

def primitive (p : polynomial α) : Prop := ∀(q : polynomial α), non_unit_const q → ¬const_divisor p q

-- Subring of constant polynomials α is isomorphic to α. Manual unfolds/rws seem the wrong approach. 
lemma c_div_if_div (a b : α) : a ∣ b → (C a) ∣ (C b) := 
begin
    sorry
end

lemma c_div_iff_div (a b : α) : a ∣ b ↔ (C a) ∣ (C b) := 
begin 
    sorry
end

lemma c_irred_iff_a_irred (a : α) : irreducible a ↔ irreducible (C a) := sorry

-- Tactic : Argue on degree. If m ∣ n, deg m < deg n or deg m = deg n = 0. deg bottoms out, and if m is const
-- use UFD-ness of α to argue irreducible factorization. 
lemma div_imp_irred_div (p m : polynomial α) (hm : m ∣ p) : ∃(n : polynomial α), (irreducible n) ∧ n ∣ p := 
begin
    by_contra hc,
    rw not_exists at hc,
    -- rw fails, even though we have hc : ∀ (x : polynomial α), ¬(irreducible x ∧ x ∣ p)
    -- rw not_and at hc, 
    have h1 : ∀(x : polynomial α), ¬irreducible x ∨ ¬x ∣ p, by {rw [not_and] at hc, exact hc}
end

lemma divisor_of_const_is_const (p q : polynomial α) (hp : is_const p) (hq : q ∣ p) : is_const q := sorry

lemma div_pq_imp_div_p_or_q (p q r : polynomial α) (hdiv : r ∣ (p * q)) (hr : irreducible r) : r ∣ p ∨ r ∣ q := sorry

lemma prod_of_prim_is_prim (p q : polynomial α) : (primitive p ∧ primitive q) → primitive (p * q) := 
begin  
    intros h_p_q, 
    by_contradiction h_pq, 
    have hp : primitive p := and.left h_p_q,
    have hq : primitive q := and.right h_p_q,
    have h_helper : ¬(∀(r : polynomial α), non_unit_const r → ¬const_divisor (p * q) r) , by exact h_pq,
    have h_helper2 : ∃r:polynomial α, ¬(non_unit_const r → ¬const_divisor (p * q) r), by exact not_forall.1 h_helper,
    have h_div : ∃(m : polynomial α), non_unit_const m ∧ const_divisor (p * q) m, by {simp [not_imp, not_not] at h_helper2, exact h_helper2}, 
    have h_irred_div : ∃(n : polynomial α), ((is_const n) ∧ (irreducible n)) ∧ const_divisor (p * q) n, by sorry, 
    apply exists.elim h_irred_div,
    intros n hn,
    -- Tactic: const divisor (C a) only divides p if a divides all coeffts of p. C a ∣ pq.
    -- If C a ∤ f, then some coefft cᵢ of f, s.t. a ∤ cᵢ. Pick the minimal such cᵢ. Similarly 
    -- if C a ∤ g, then there exists coefft dⱼ of g, s.t. a ∤ dⱼ. coefft k of x^(i+j) will 
    -- be k = ∑cₘdₙ, where m + n = i + j. Except when m = i and n = j, either m < i or n < j
    -- so a ∣ cₘdₙ. But a ∤ cᵢdⱼ. Hence a ∤ k. Contradiction. 
    -- Tactic 2 : n irred → n prime by polynomial α being domain.
    have h_n_div : (n ∣ p) ∨ (n ∣ q), by sorry, 
    have h_npq : ¬primitive p ∨ ¬primitive q, by sorry,
    show false,
         cases h_npq,
            contradiction,
            contradiction
end


def to_quot (a : α) : quotient_ring α := ⟦(a, (1 : non_zero_divisors α))⟧

def quot_poly (p : polynomial α) : polynomial (quotient_ring α) := p.map to_quot

lemma has_primitive_factorisation (p : polynomial α) : ∃(c : α) (p' : polynomial α), primitive p' ∧ C c * p' = p := sorry       

-- Not sure how to approach this. Normal proof is just multiplying through by the lcm of the denominators of the coeffts in 
-- reduced form. But I've failed to find the notion of a reduced form.
lemma quot_poly_mult (p : polynomial (quotient_ring α)) : ∃(c : α) (d : polynomial α), quot_poly (C c) * p = quot_poly d := sorry 

lemma irred_in_base_imp_irred_in_quot {p : polynomial α} (hp_p : primitive p) (hp_ir : irreducible p) (hp_nc : ¬is_const p) : irreducible (quot_poly p) := 
begin 
    let p' := quot_poly p,
    by_contradiction h_contr,
    have h1: ∃(m n : polynomial (quotient_ring α)), (¬ is_unit m) ∧ (¬ is_unit n) ∧ m * n = p', by sorry,
    apply exists.elim h1,
    intros m hm,
    apply exists.elim hm,
    intros n h_prod, -- ideally both apply and intros should be a single statement
    have h2: ∃ (c : α) (d : polynomial α), quot_poly (C c) * m = quot_poly d, by exact quot_poly_mult m, 
    apply exists.elim h2,
    intros c hc,
    apply exists.elim hc,
    intros d hd,
    have h3: ∃(c₂ : α) (d₂ : polynomial α), quot_poly (C c₂) * n = quot_poly d₂, by exact quot_poly_mult n, 
    apply exists.elim h3,
    intros c₂ hc₂,
    apply exists.elim hc₂,
    intros d₂ hd₂,

end
