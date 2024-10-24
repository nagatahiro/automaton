module record1 where

record _∧_ (A B : Set) : Set where
  field
     π1 : A
     π2 : B

ex0 : {A B : Set} → A ∧ B →  A
ex0 =  _∧_.π1 

ex1 : {A B : Set} → ( A ∧ B ) → A 
ex1 a∧b =  _∧_.π1 a∧b

open _∧_

ex0' : {A B : Set} → A ∧ B →  A
ex0' =  π1 

ex1' : {A B : Set} → ( A ∧ B ) → A 
ex1' a∧b =  π1 a∧b

ex2 : {A B : Set} → ( A ∧ B ) → B 
ex2 a∧b = {!!}

ex3 : {A B : Set} → A → B → ( A ∧ B ) 
ex3 a b = {!!}

ex4 : {A B : Set} → A → ( A ∧ A ) 
ex4 a  = record { π1 = {!!} ;  π2 = {!!} }

ex5 : {A B C : Set} → ( A ∧ B ) ∧ C  →  A ∧ (B ∧ C) 
ex5 a∧b∧c = record { π1 = {!!} ; π2 = {!!} }

--
--                                 [(A → B ) ∧ ( B →  C) ]₁  
--                                ──────────────────────────────────── π1
--     [(A → B ) ∧ ( B →  C) ]₁        (A → B )    [A]₂
--   ──────────────────────────── π2 ─────────────────────── λ-elim
--          ( B →  C)                     B
--   ─────────────────────────────────────────── λ-elim
--                   C
--   ─────────────────────────────────────────── λ-intro₂
--                 A → C
--   ─────────────────────────────────────────── λ-intro₁
--     ( (A → B ) ∧ ( B →  C) )  → A → C

ex6 : {A B C : Set} → ( (A → B ) ∧ ( B →  C) )  → A → C
ex6 x a = {!!}

ex6' : {A B C : Set} →  (A → B ) → ( B →  C)   → A → C
ex6' = {!!}

