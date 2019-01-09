import data.polynomial
import ring_theory.unique_factorization_domain

open polynomial
open classical

universes u 

variables {α : Type u} {a: α} 

variables [integral_domain α] {p q r s : polynomial α}
variable [decidable_eq α]
variable [unique_factorization_domain α]
variable [has_mod α]

-- 
theorem has_R_root_imp_has_frac_R_root (p : polynomial α) : (p = p) := sorry

def has_non_unit_divisor (a : α) : Prop := ∃(b : α), (¬is_unit b) ∧ (b ∣ a)

lemma non_unit_div_ab_imp_non_unit_div_a_or_non_unit_div_b (a b : α) : ∃(c : α), 
    (¬is_unit c) ∧ (c ∣ (a * b)) → (has_non_unit_divisor a) ∨ (has_non_unit_divisor b) := sorry

-- def primitive (p : polynomial α) : Prop :=
-- ¬(∃(a : α), ∃(r : polynomial α), (¬is_unit a) ∧ p = (C a) * r)

def is_const (p : polynomial α) : Prop := degree p = 0 

instance is_const.decidable : decidable (is_const p) :=
by unfold is_const; apply_instance

def mod_by_const : Π (p : polynomial α) {q : polynomial α},
  is_const q → polynomial α
| p := λ q hq, 
    if h: is_const q then 
        let 
            z := C ((leading_coeff p) % (leading_coeff q)) * X^(nat_degree p),
            rem := p - C (leading_coeff p) * X^(nat_degree p)
                in 
                    if h2: (nat_degree p = 0) then 
                        z 
                    else 
                        z + (mod_by_const rem hq)
    else 
        p 
    


lemma mod_well_founded ()

-- def mod_by_const (p q : polynomial α) : polynomial α := 
-- if hq : is_const q then (div_mod_by_const_aux p hq).2 else p 

-- def non_primitive (p : polynomial α) : Prop :=
-- ∃(a : α), 

-- lemma not_prim_imp_factors (p : polynomial α) [¬primitive p] : ∃(a : α), ()

-- lemma prod_of_prim_is_prim (p q : polynomial α) [primitive p] [primitive q] : primitive (p * q) :=
-- by_contradiction
--     (assume ch : ¬(primitive (p * q)),
--         have ch2 : ¬¬(∃(a : α), ∃(r : polynomial α), (¬is_unit a) ∧ (p * q = C a * r)), from ch,
--         have ch2_5 : (∃(a : α), ∃(r : polynomial α), (¬is_unit a) ∧ (p * q = C a * r)), from sorry, -- double not elim on ch2
--         have ch3 : leading_coeff (p * q) = (leading_coeff p) * (leading_coeff q), by simp,
--         have ch4 :  (has_non_unit_divisor (leading_coeff p)) ∨ (has_non_unit_divisor (leading_coeff p)), by sorry,
        
--         show false, from sorry)


