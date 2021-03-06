import data.polynomial
import ring_theory.unique_factorization_domain
import order.bounded_lattice
import ring_theory.localization
import data.set
import data.nat.basic
import tactic.rewrite

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

def primitive (p : polynomial α) : Prop := 
    ∀(q : polynomial α), non_unit_const q → ¬const_divisor p q

-- Subring of constant polynomials α is isomorphic to α. Manual unfolds/rws or producing an explicit divisor seem the wrong approach. 
lemma c_div_if_div (a b : α) : a ∣ b → (C a) ∣ (C b) := sorry

lemma c_div_iff_div (a b : α) : a ∣ b ↔ (C a) ∣ (C b) := sorry

lemma c_irred_iff_irred (a : α) : irreducible a ↔ irreducible (C a) := sorry

-- Tactic : Argue on degree. If m ∣ n, deg m < deg n or deg m = deg n = 0. deg bottoms out, and if m is const
-- use UFD-ness of α to argue irreducible factorization. 
lemma div_imp_irred_div {p m : polynomial α} (hm : m ∣ p) (hm' : ¬is_unit m) : ∃(n : polynomial α), (irreducible n) ∧ n ∣ p := 
begin
    cases em (irreducible m),
    have h_and : _ := and.intro h hm,
    apply exists.intro m h_and,
     
    by_contradiction hc,
    rw not_exists at hc,
    simp [not_and] at hc,

    have h1 : ∃(a : α), ¬is_unit a ∧ C a ∣ p, by sorry,
    rcases h1 with ⟨a,ha⟩,
    have h_non_unit := and.left ha,
    have h_div := and.right ha,
    
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
lemma div_pq_imp_div_p_or_q {p q : polynomial α} {r: α} (hdiv : C r ∣ (p * q)) 
    (hr : irreducible r) : C r ∣ p ∨  C r ∣ q :=
begin 
    let I : ideal (polynomial α) := ideal.span (singleton (C r)),
    have h1 : ∀(f : polynomial α),  (C r) ∣ f ↔ ideal.quotient.mk I f = 0, by sorry,
    have h2 : _ := h1 (p * q),
    have h3 : _ := h2.1 hdiv,
    -- have h4 : (ideal.quotient.mk I p = 0) ∨ (ideal.quotient.mk I q = 0), by sorry, -- Integral Domain I -- leads to deterministic timeout
    have h5 : C r ∣ p ∨  C r ∣ q, by sorry,
    exact h5
end

lemma prod_of_prim_is_prim (p q : polynomial α) : 
    (primitive p ∧ primitive q) → primitive (p * q) := 
begin  
    intros h_p_q, 
    by_contradiction h_pq, 
    have hp : primitive p := and.left h_p_q,
    have hq : primitive q := and.right h_p_q,
    have h_helper : ¬(∀(r : polynomial α), non_unit_const r → ¬const_divisor (p * q) r)  := h_pq,
    have h_helper2 : ∃r:polynomial α, ¬(non_unit_const r → ¬const_divisor (p * q) r) := not_forall.1 h_helper,
    have h_div : ∃(m : polynomial α), non_unit_const m ∧ const_divisor (p * q) m, by {simp [not_imp, not_not] at h_helper2, exact h_helper2}, 
    rcases h_div with ⟨m, hm⟩,

    have h_irred_div : ∃(n : α), (irreducible n) ∧ ((C n) ∣ (p * q)), by sorry, 
    rcases h_irred_div with ⟨n, hn⟩,
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

-- set c = gcd coeffts. But where is gcd for more than 2 elems?
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
    -- show false, from hc haq.symm,
    show false, from hc.symm haq,
    show false, from h_non_unit hp'
end

lemma unit_is_const {p : polynomial γ} (hp : is_unit p) : is_const p := 
begin 
    have h1: degree p = 0 := degree_eq_zero_of_is_unit hp,
    have h2 : p ≠ 0, by sorry,
    have h3 : nat_degree p = 0, by sorry,
    rwa [←is_const] at h3
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

lemma not_irred_imp_prod {γ : Type*} [monoid γ] [decidable_eq γ]  {p : γ} (hp : ¬irreducible p) (hp' : ¬is_unit p) : 
    ∃(m n : γ),   p = m * n  ∧ (¬ is_unit m) ∧ (¬ is_unit n) :=
begin 
    unfold irreducible at hp,
    rw [not_and_distrib, not_not, not_forall] at hp,
    simp [hp'] at hp,
    simp [not_forall,not_imp,not_or_distrib] at hp,
    exact hp
end

lemma nat_deg_quot_poly_eq_nat_deg_poly (p : polynomial α) : nat_degree p = nat_degree (quot_poly p) := 
begin 
    sorry
end

lemma const_iff_quot_poly_const {p : polynomial α} : is_const p ↔ is_const (quot_poly p) := sorry

lemma quot_poly_coe (a : α): quot_poly (C a) = (C (to_quot a)) := 
begin 
    unfold quot_poly,
    unfold map, 
    sorry
end 

instance quot_poly.is_semiring_hom : is_semiring_hom (quot_poly : polynomial α → polynomial (quotient_ring α)) := 
begin 
    have h1 : quot_poly 1 = (1 : polynomial (quotient_ring α)), by sorry,
    have h0 : quot_poly 0 = (0 : polynomial (quotient_ring α)), by refl,
    refine_struct {..};
    sorry
end

instance to_quot.is_semiring_hom : is_semiring_hom (to_quot : α → quotient_ring α) := 
begin 
    sorry
end 

lemma can_factor_poly_helper (a b : α) : quot_poly (C (a * b)) * C ((to_quot (a * b))⁻¹) = 1 := 
begin 
    have h1: quot_poly (C (a * b)) = (C (to_quot (a*b))), by rw quot_poly_coe,
    rw h1,
    rw ←C.is_semiring_hom.map_mul,
    have h2 : to_quot (a * b) * (to_quot (a * b))⁻¹ = 1, by sorry, -- by simp, -- mul_right_inv (to_quot (a * b)),
    rw [h2],
    refl
end 


lemma quot_poly_of_non_const_is_non_unit {p : polynomial α} (hp : ¬is_const p) : ¬is_unit (quot_poly p) := sorry

lemma rearrange_lemma (d' d₂' : polynomial α) (c' c₂' : α) : quot_poly (C c' * d') * quot_poly (C c₂' * d₂') = quot_poly (C c' * C c₂') * quot_poly (d' * d₂') := 
begin 
    simp [quot_poly.is_semiring_hom.map_mul],
    ring
end

-- coeffts in LHS all all integers, so coeffts on the right must be all integers. q is primitive, so no k divides all coeffts of q 
-- follows that r must be an integer. Adapt Case 2 from old proof. 
lemma prim_associate {p q : polynomial α} {r : quotient_ring α} 
    (h : quot_poly p = C r * quot_poly q) : ∃(k : α), to_quot k = r := 
begin 
    sorry
end

lemma can_factor_poly (p : polynomial α) (hp: ¬is_const p) (h_nir : ¬irreducible (quot_poly p)) : 
    ∃(d' d₂' : polynomial α), ∃(k : quotient_ring α), quot_poly p = 
        quot_poly (d' * d₂') *  (C k) ∧ primitive d' ∧ primitive d₂' := 
begin 
    have h0 : ¬ is_unit (quot_poly p) := quot_poly_of_non_const_is_non_unit hp,
    rcases not_irred_imp_prod h_nir h0 with ⟨m, n, h_p_eq_mn, hc⟩,
    -- ∃ (c : α) (d : polynomial α), quot_poly (C c) * m = quot_poly d
    rcases quot_poly_mult m with ⟨c,d,h_cm_eq_d⟩, 
    -- ∃(c' : α) (d' : polynomial α), (primitive d') ∧ ((C c') * d' = d)
    rcases has_primitive_factorisation d with ⟨c', d', primd, rfl⟩,
    rcases quot_poly_mult n with ⟨c₂,d₂,h_c₂n_eq_d₂⟩, 
    -- ∃(c₂' : α) (d₂' : polynomial α), (primitive d₂') ∧ ((C c₂') * d₂' = d₂)
    rcases has_primitive_factorisation d₂ with ⟨c₂', d₂', primd₂, rfl⟩,
    
    have h5  : (quot_poly (C c) * m) * quot_poly (C c₂) * n = quot_poly (C c' * d') * quot_poly (C c₂' * d₂'), 
        begin rw [h_cm_eq_d, mul_assoc, h_c₂n_eq_d₂], end, -- It would be lovely if rw_assoc worked here.
    have h6  : quot_poly (C c' * d') * quot_poly (C c₂' * d₂') = quot_poly p * quot_poly (C (c * c₂)), from calc
               quot_poly (C c' * d') * quot_poly (C c₂' * d₂') = (quot_poly (C c) * m) * quot_poly (C c₂) * n : by exact h5.symm
                                                           ... = m * n * quot_poly (C c) * quot_poly (C c₂) : by ring
                                                           ... = quot_poly p * quot_poly (C c) * quot_poly (C c₂) : by rw ←h_p_eq_mn
                                                           ... = quot_poly p * quot_poly ((C c) * (C c₂)) : by begin rw mul_assoc, rw ←quot_poly.is_semiring_hom.map_mul end
                                                           ... = quot_poly p * quot_poly (C (c * c₂)) : by rw ←C.is_semiring_hom.map_mul,
    have h6' : quot_poly p * quot_poly (C (c * c₂)) * C ((to_quot (c * c₂))⁻¹) = quot_poly (C c' * C c₂') * quot_poly (d' * d₂')  * C ((to_quot (c * c₂))⁻¹), by {rw [rearrange_lemma] at h6, rw h6},
    have h7  : quot_poly p = quot_poly (C c' * C c₂') * quot_poly (d' * d₂') *  C ((to_quot (c * c₂))⁻¹), by {rw [mul_assoc, can_factor_poly_helper, mul_one] at h6', exact h6'}, 
    have h9 : quot_poly p = quot_poly (d' * d₂') * C ((to_quot (c * c₂))⁻¹ * to_quot (c' *c₂')), from calc 
             quot_poly p = quot_poly (C c' * C c₂') * quot_poly (d' * d₂') *  C ((to_quot (c * c₂))⁻¹) : by exact h7
                    ...  = quot_poly (d' * d₂') * C ((to_quot (c * c₂))⁻¹) * quot_poly (C c' * C c₂') : by rw [mul_assoc, mul_comm]
                    ...  = quot_poly (d' * d₂') * C ((to_quot (c * c₂))⁻¹) * quot_poly (C (c' * c₂')) : by rw ←C.is_semiring_hom.map_mul
                    ...  = quot_poly (d' * d₂') * C ((to_quot (c * c₂))⁻¹) * C (to_quot (c' *c₂')) : by rw quot_poly_coe
                    ...  = quot_poly (d' * d₂') * C ((to_quot (c * c₂))⁻¹ * to_quot (c' *c₂')) : by rw [mul_assoc, ←C.is_semiring_hom.map_mul],

    let k  := (to_quot (c * c₂))⁻¹ * to_quot (c' *c₂'),
    have h_k : k = (to_quot (c * c₂))⁻¹ * to_quot (c' *c₂'), by refl,
    have h10 : quot_poly p = quot_poly (d' * d₂') * C (k), by {rw ←h_k at h9, exact h9}, 
    have h11 : quot_poly p = quot_poly (d' * d₂') * C (k) ∧ primitive d' ∧ primitive d₂' := ⟨h10, primd, primd₂⟩,
    have h12 : ∃(k : quotient_ring α), quot_poly p = quot_poly (d' * d₂') * C (k) ∧ primitive d' ∧ primitive d₂' := exists.intro k h11,
    have h13 : _ := exists.intro d₂' h12,
    have h14 : _ := exists.intro d' h13,
    exact h14
end 
