import data.polynomial
import ring_theory.unique_factorization_domain
import order.bounded_lattice
import ring_theory.localization
import data.set
import data.nat.basic

open ideal
open polynomial
open classical
open localization
open set
open nat

local attribute [instance, priority 0] classical.prop_decidable

universe u 

variables {α : Type u} {a: α}  
variables {γ : Type u} [decidable_eq γ] [integral_domain γ] [unique_factorization_domain γ] 

variables [integral_domain α] {p q r s : polynomial α}
variable [decidable_eq α]
variable [unique_factorization_domain α]
variable [has_mod α]

-- set_option pp.all true

def is_const {γ : Type*} [comm_semiring γ] [decidable_eq γ] (p : polynomial γ) : Prop := nat_degree p = 0

instance is_const.decidable : decidable (is_const p) :=
by unfold is_const; apply_instance

def non_unit_const (p : polynomial α) : Prop := (is_const p) ∧ (¬is_unit p)

lemma not_const_imp_non_zero  : ¬is_const p → p ≠ (0 : polynomial α) := 
mt begin 
 intro hp,
 show is_const p, by {rw [hp, is_const], simp}
end

def const_divisor : Π (p q : polynomial α),  Prop 
| p q := is_const q ∧ q ∣ p

def primitive (p : polynomial α) : Prop := ∀(q : polynomial α), non_unit_const q → ¬const_divisor p q

-- Subring of constant polynomials α is isomorphic to α. Manual unfolds/rws or producing an explicit divisor seem the wrong approach. 
lemma c_div_if_div (a b : α) : a ∣ b → (C a) ∣ (C b) := sorry

lemma c_div_iff_div (a b : α) : a ∣ b ↔ (C a) ∣ (C b) := sorry

lemma c_irred_iff_irred (a : α) : irreducible a ↔ irreducible (C a) := sorry

-- Tactic : Argue on degree. If m ∣ n, deg m < deg n or deg m = deg n = 0. deg bottoms out, and if m is const
-- use UFD-ness of α to argue irreducible factorization. 
lemma div_imp_irred_div (p m : polynomial α) (hm : m ∣ p) (hm' : ¬is_unit m) : ∃(n : polynomial α), (irreducible n) ∧ n ∣ p := 
begin
    cases em (irreducible m),
    have h_and : _ := and.intro h hm,
    apply exists.intro m h_and,
     
    by_contradiction hc,
    rw not_exists at hc,
    
end

lemma divisor_of_const_is_const (p q : polynomial α) (hp : is_const p) (hq : q ∣ p) : is_const q := 
begin 
    have h1 : nat_degree q ≤ nat_degree p := sorry,
    have h3 : nat_degree q = 0 := sorry,
    rw ←is_const at h3,
    exact h3
end

-- Tactic : n irred → n prime as a const by UFD. α/(n) is domain, so α/(n)[x] is domain
-- n ∣ pq, so pq vanishes in α/(n)[x]. Hence p vanishes or q vanishes. But poly p vanishes
-- iff n ∣ p. n ∣ p or n ∣ q. 
-- α →  α[x]
-- ↓    ↓
-- α(n) →α/(n)[x]
lemma div_pq_imp_div_p_or_q (p q : polynomial α) (r: α) (hdiv : C r ∣ (p * q)) (hr : irreducible r) : C r ∣ p ∨  C r ∣ q :=
begin 
    have h1: prime r := sorry,
    have  
end

lemma prod_of_prim_is_prim (p q : polynomial α) : (primitive p ∧ primitive q) → primitive (p * q) := 
begin  
    intros h_p_q, 
    by_contradiction h_pq, 
    have hp : primitive p := and.left h_p_q,
    have hq : primitive q := and.right h_p_q,
    have h_helper : ¬(∀(r : polynomial α), non_unit_const r → ¬const_divisor (p * q) r) , by exact h_pq,
    have h_helper2 : ∃r:polynomial α, ¬(non_unit_const r → ¬const_divisor (p * q) r), by exact not_forall.1 h_helper,
    have h_div : ∃(m : polynomial α), non_unit_const m ∧ const_divisor (p * q) m, by {simp [not_imp, not_not] at h_helper2, exact h_helper2}, 
    have h_irred_div : ∃(n : α), (irreducible n) ∧ const_divisor (p * q) (C n), by sorry, 
    apply exists.elim h_irred_div,
    intros n hn,
    have h_n_div : (C n ∣ p) ∨ (C n ∣ q), by sorry, 
    have h_npq : ¬primitive p ∨ ¬primitive q, by sorry,
    show false,
         cases h_npq,
            contradiction,
            contradiction
end


def to_quot (a : α) : quotient_ring α := ⟦(a, (1 : non_zero_divisors α))⟧

def is_integer (q : quotient_ring α) : Prop := ∃(a : α), to_quot a = q

def quot_poly (p : polynomial α) : polynomial (quotient_ring α) := p.map to_quot

-- set c = gcd coeffts. 
lemma has_primitive_factorisation (p : polynomial α) : ∃(c : α) (p' : polynomial α), primitive p' ∧ C c * p' = p := sorry       

lemma quot_poly_mult (p : polynomial (quotient_ring α)) : ∃(c : α) (d : polynomial α), quot_poly (C c) * p = quot_poly d := sorry 

lemma non_unit_divisor_imp_not_irred {p q : polynomial α} (h_divisor : q ∣ p) (h_non_unit : ¬is_unit q) (h_neq : ∀(a : polynomial α), is_unit a → a * q ≠ p) : ¬irreducible p :=
begin 
    by_contradiction hp,
    dsimp [irreducible] at hp,
    have h1: ¬is_unit p, by sorry, -- non unit q cannot divide unit p
    simp [h1] at hp,
    have h2: ∃(a : polynomial α), p = a * q , by sorry, -- divisibility
    rcases h2 with ⟨a, haq⟩,
    have hp' := hp a q,
    have h_neq' := h_neq a,
    simp [haq] at hp',
    cases hp',
    have hc := h_neq' hp',
    show false, from hc (eq.symm haq),
    -- show false, from (eq.symm hc) haq fails
    show false, from h_non_unit hp'
end

lemma irred_imp_prim (p : polynomial α) (hp_nc : ¬is_const p) (hp : irreducible p): primitive p :=  
begin 
    by_contradiction hc,
    rcases (not_forall.1 hc) with ⟨q, hq⟩,
    rw [not_imp, not_not] at hq,
    have h_non_unit_const : _ := and.left hq,
    have h_non_unit : _ := and.right h_non_unit_const,
    have h_const_divisor : _ := and.right hq,
    have h_divisor : _ := and.right h_const_divisor,
    have h_const : _ := and.left h_const_divisor,
    have h_non_multiple : ∀(a : polynomial α), is_unit a → a * q ≠ p := sorry, -- unit multiple of a const can't be a non-const
    have h_not_irred_p : _ := non_unit_divisor_imp_not_irred h_divisor h_non_unit h_non_multiple,
    show false, from h_not_irred_p hp
end

lemma unit_is_const {p : polynomial γ} (hp : is_unit p) : is_const p := 
begin 
    sorry
end


lemma not_irred_imp_non_unit_divisors {γ : Type*} [monoid γ] [decidable_eq γ] {p : γ} (hp : ¬irreducible p) (hp' : ¬is_unit p) : ∃(m n : γ),   p = m * n  ∧ (¬ is_unit m) ∧ (¬ is_unit n) :=
begin 
    unfold irreducible at hp,
    rw [not_and_distrib, not_not, not_forall] at hp,
    simp [hp'] at hp,
    simp [not_forall,not_imp,not_or_distrib] at hp,
    exact hp
end

lemma const_iff_quot_poly_const {p : polynomial α} : is_const p ↔ is_const (quot_poly p) := sorry

lemma irred_in_base_imp_irred_in_quot {p : polynomial α} (hp_ir : irreducible p) (hp_nc : ¬is_const p) : irreducible (quot_poly p) :=
begin 
    by_contradiction h_contr, 
    have h_not_quot_poly_const : ¬is_const (quot_poly p) := sorry, 
    have h0 : ¬ is_unit (quot_poly p) := sorry,
    -- ∃(m n : polynomial (quotient_ring α)), (¬ is_unit m) ∧ (¬ is_unit n) ∧ m * n = p'
    rcases not_irred_imp_non_unit_divisors h_contr h0 with ⟨m, n, p_eq_mn, hc⟩,
    -- ∃ (c : α) (d : polynomial α), quot_poly (C c) * m = quot_poly d
    rcases quot_poly_mult m with ⟨c,d,h_cm_eq_d⟩, -- NOTE rfling  h_cm_eq_d produces an error
    -- ∃(c' : α) (d' : polynomial α), (primitive d') ∧ ((C c') * d' = d)
    rcases has_primitive_factorisation d with ⟨c', d', primd, rfl⟩,
    rcases quot_poly_mult n with ⟨c₂,d₂,h_c₂n_eq_d₂⟩, -- NOTE rfling  h_c₂n_eq_d₂ produces an error
    -- ∃(c₂' : α) (d₂' : polynomial α), (primitive d₂') ∧ ((C c₂') * d₂' = d₂)
    rcases has_primitive_factorisation d₂ with ⟨c₂', d₂', primd₂, rfl⟩,

    sorry
end 


-- -- deterministic time out for some reason now
-- lemma irred_in_base_imp_irred_in_quot' {p : polynomial α} (hp_ir : irreducible p) (hp_nc : ¬is_const p) : irreducible (quot_poly p) := 
-- begin 
--     let p' := quot_poly p,
--     by_contradiction h_contr,
--     have h1: ∃(m n : polynomial (quotient_ring α)), (¬ is_unit m) ∧ (¬ is_unit n) ∧ m * n = p', by sorry, -- by h_contr
--     apply exists.elim h1,
--     intros m hm,
--     apply exists.elim hm,
--     intros n h_prod, -- ideally both apply and intros should be a single statement
--     have h2: ∃ (c : α) (d : polynomial α), quot_poly (C c) * m = quot_poly d, by exact quot_poly_mult m, 
--     apply exists.elim h2,
--     intros c hc,
--     apply exists.elim hc,
--     intros d hd,
--     -- rcases has_primitive_factorisation d with ⟨c', d', primd, rfl⟩,
--     have h2_irred : ∃(c' : α) (d' : polynomial α), (primitive d') ∧ ((C c') * d' = d) := has_primitive_factorisation d,
--     apply exists.elim h2_irred,
--     intros c' hc',
--     apply exists.elim hc',
--     intros d' hd',
--     have h3: ∃(c₂ : α) (d₂ : polynomial α), quot_poly (C c₂) * n = quot_poly d₂, by exact quot_poly_mult n, 
--     apply exists.elim h3,
--     intros c₂ hc₂,
--     apply exists.elim hc₂,
--     intros d₂ hd₂,
--     have h3_irred : ∃(c₂' : α) (d₂' : polynomial α), (primitive d₂') ∧ ((C c₂') * d₂' = d₂), by exact has_primitive_factorisation d₂,
--     apply exists.elim h3_irred,
--     intros c₂' hc₂',
--     apply exists.elim hc₂',
--     intros d₂' hd₂',
--     have h4 : quot_poly (C c₂) * n * quot_poly (C c) * m = quot_poly d₂ * quot_poly d, by sorry, -- simp
--     have h5 : m * n = quot_poly d₂ * quot_poly d *  C (has_inv.inv (to_quot c)) * C (has_inv.inv (to_quot c₂)), by sorry, --simp
--     -- have h6 : quot_poly p = quot_poly d₂ * quot_poly d * C (has_inv.inv (to_quot (c * c₂))), by {rw h_prod.right.right at h5, exact h5}, -- including this line causes a deterministic timeout
--     have h7 : quot_poly p = quot_poly (d' * d₂') *  C (has_inv.inv (to_quot (c' * c₂'))), by sorry, -- simp/coe of h6 - shouldn't matter if we coe along poly first or to quot first.
--     -- LHS has integer coeffts, so RHS has integer coeffts.
--     -- p is primitive, d',d₂' are primtive. So if  (1/quot_poly (C c)) * (1/quot_poly (C c₂)) ≠ 1 contradiction. 
--     -- if = 1, then produced a factorisation for p. contradiction. 
--     cases em (is_unit (c * c₂)),
--         -- Case 1
--         have h_const : ∃(k : α), (to_quot k) = has_inv.inv (to_quot (c' * c₂')), by sorry, -- by to_quot inv (c * c₂) = int to_quot (c * c₂) coe lemma
--         apply exists.elim h_const,
--         intros k hk,
--         have h8 : quot_poly p = quot_poly (d' * d₂') * C (to_quot k), by rwa ←hk at h7,
--         have h8' : quot_poly p = quot_poly (d' * d₂') * quot_poly (C k), by sorry, -- Simplifier
--         have h9 : quot_poly p = quot_poly(d' * (C k) * d₂'), by sorry, -- Simplifier
--         have h10 : p = d * ((C k) * d₂'), by sorry, -- coe lemma
--         have h10' : ¬irreducible p, by sorry, -- as in irred_imp_prim, have witness for reduciblilty
--         show false, from h10' hp_ir,
--         -- case 2 
--         have h_coeff_eq : ∀(n : ℕ), coeff p' n = coeff (quot_poly (d' * d₂') *  C (has_inv.inv (to_quot (c' * c₂')))) n, by sorry,
--         have h_p_coeff : ∀ (n : ℕ), coeff p' n = to_quot (coeff p n), by sorry, 
--         have h_p_coeff' : ∀(n: ℕ), coeff (quot_poly (d' * d₂') *  C (has_inv.inv (to_quot (c' * c₂')))) n = to_quot (coeff p n), by sorry,
--         have h_coeff : ∀(n : ℕ), coeff (quot_poly (d' * d₂') *  C (has_inv.inv (to_quot (c' * c₂')))) n = coeff (quot_poly (d' * d₂')) n * has_inv.inv (to_quot (c' * c₂')), by sorry,
--         have h_d_d2_prim : primitive (d' * d₂'), by exact (prod_of_prim_is_prim d' d₂' (and.intro (hd'.left) (hd₂'.left))),
--         have h8 : ∀(n : ℕ), coeff p' n =  coeff (quot_poly (d' * d₂')) n * has_inv.inv (to_quot (c' * c₂')), by sorry, 
--         have h9 : ∀(n : ℕ), to_quot (coeff p n) = coeff (quot_poly (d' * d₂')) n * has_inv.inv (to_quot (c' * c₂')), by sorry, 
--         have h9' : ∀(n : ℕ), to_quot (c' * c₂') * to_quot (coeff p n) = coeff (quot_poly (d' * d₂')) n, by sorry,
--         have h10 : ∀(n : ℕ), to_quot (c' * c₂' * coeff p n) = coeff (quot_poly (d' * d₂')) n, by sorry, 
--         have h11 : ∀(n : ℕ), c' * c₂' ∣ coeff (d' * d₂') n, by sorry, 
--         have h12 : ¬primitive (d' * d₂'), by sorry,
--         show false, from h_d_d2_prim h12
-- end