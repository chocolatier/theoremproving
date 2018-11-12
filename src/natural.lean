inductive N : Type 
| z : N 
| s : N -> N 

open N

def plus : N -> N -> N 
| x z := x 
| x (s y) := s (plus x y)

def mult : N -> N -> N 
| z x := z 
| (s y) x := plus (mult y x) x

theorem zero_mult (n : N) : mult z n = z := rfl
theorem zero_plus (x : N): plus x z = x := rfl
theorem succ_mult (a b : N) : mult (s a) b = plus (mult a b) b := rfl

theorem zero_id (x : N) : plus z x = x := 
N.rec_on x 
    (show plus z z = z, by refl)
    (assume x,
        assume ih: plus z x = x,
        show plus z (s x) = (s x), from calc
             plus z (s x) = s (plus z x) : by refl
                      ... = s x : by rw ih)

theorem assoc_plus (a b c : N) : plus (plus a b) c = plus a (plus b c) := 
N.rec_on c
    (show plus (plus a b) z = plus a (plus b z), by rw [zero_plus, zero_plus])
    (assume c,
        assume ih: plus (plus a b) c = plus a (plus b c),
        show plus (plus a b) (s c) = plus a (plus b (s c)), from calc
             plus (plus a b) (s c) = s (plus (plus a b) c) : by refl 
                               ... = s (plus a (plus b c)) : by rw ih
                               ... = plus a (s (plus b c)) : by refl 
                               ... = plus a (plus b (s c)) : by refl 
    )

theorem move_succ (a b : N) : plus a (s b) = plus (s a) b := 
    N.rec_on b 
    (show plus (s a) z = plus a (s z), by refl)
    (assume b,
        assume ih: plus a (s b) = plus (s a) b,
        show plus a (s (s b)) = plus (s a) (s b), from calc
             plus a (s (s b)) = s (plus a (s b)) : by refl
                          ... = s (plus (s a) b) : by rw ih
                          ... = (plus (s a) (s b)): by refl
            )

theorem comm_plus (a b : N) : plus a b = plus b a  := 
N.rec_on b
    (show plus a z = plus z a, by rw [zero_id, zero_plus])
    (assume b,
        assume ih: plus a b = plus b a,
        show plus a (s b) = plus (s b) a, from calc
             plus a (s b) = s (plus a b) : by refl 
                      ... = s (plus b a) : by rw ih 
                      ... = plus b (s a) : by refl
                      ... = plus (s b) a : by rw move_succ
        )

theorem distr (a b c : N) : mult a (plus b c) = plus (mult a b) (mult a c) :=
N.rec_on a 
    (show mult z (plus b c) = plus (mult z b) (mult z c), by rw [zero_mult, zero_mult, zero_mult, zero_plus])
    -- (show mult (s a) (plus b c) = plus (mult a (plus b c)) (plus b c), by rw [succ_mult])
    (assume a,
        assume ih : mult a (plus b c) = plus (mult a b) (mult a c),
        show mult (s a) (plus b c) = plus (mult (s a) b) (mult (s a) c), from calc  
             mult (s a) (plus b c) = plus (mult a (plus b c)) (plus b c)          : by rw succ_mult
                               ... = plus (plus (mult a b) (mult a c)) (plus b c) : by rw [ih]
                               ... = plus (mult a b) (plus (mult a c) (plus b c)) : by rw assoc_plus 
                               ... = plus (mult a b) (plus (plus b c) (mult a c)) : by rw comm_plus _ (plus b c)
                               ... = plus (plus (mult a b) (plus b c)) (mult a c) : by rw <-assoc_plus _ _ (mult a c)
                               ... = plus (plus (plus (mult a b) b) c) (mult a c) : by rw <-assoc_plus
                               ... = plus (plus (mult (s a) b) c) (mult a c)      : by rw succ_mult
                               ... = plus (mult (s a) b) (plus c (mult a c))      : by rw assoc_plus 
                               ... = plus (mult (s a) b) (plus (mult a c) c)      : by rw comm_plus _ c 
                               ... = plus (mult (s a) b) (mult (s a) c)           : by rw succ_mult _ c
        )
