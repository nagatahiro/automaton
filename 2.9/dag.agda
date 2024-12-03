module dag where

--         f0
--       -----→
--    t0         t1
--       -----→
--         f1


data  TwoObject   : Set  where     -- vertex
    t0 : TwoObject
    t1 : TwoObject


data TwoArrow  : TwoObject → TwoObject → Set  where  -- edge
    f0 :  TwoArrow t0 t1
    f1 :  TwoArrow t0 t1


--         r0
--       -----→
--    t0         t1
--       ←-----
--         r1

data Circle  : TwoObject → TwoObject → Set  where
    r0 :  Circle t0 t1
    r1 :  Circle t1 t0

--
-- Definition of ⊥ and ¬  in agda
--

data ⊥ : Set where              -- data with no consutructor

⊥-elim : {A : Set } → ⊥ →  A    -- function with no possible input
⊥-elim ()                       --   no constructor

¬_ : Set → Set                  -- A won't happen (This is a type, not an imlemetation )
¬ A = A → ⊥

data Bool  : Set  where
    true :  Bool
    false :  Bool

data connected { V : Set } ( E : V → V → Set ) ( x y : V ) : Set  where
    direct :     E x y → connected E x y 
    indirect :  { z : V  } → E x z  →  connected {V} E z y → connected E x y

-- this is similar to the List
data List ( A : Set ) : Set where
    nil : List A
    cons : A → List A →  List A

lemma1 : connected TwoArrow t0 t1
lemma1 = direct f0

lemma2 : ¬ ( connected TwoArrow t1 t0 )
lemma2 (direct p) = ⊥-elim p
lemma2 (indirect {z} p q) = ⊥-elim p

lemma3 : connected Circle t0 t0
lemma3 = indirect r0 (direct r1)

-- decidabity

data Dec (P : Set) : Set where
   yes :   P → Dec P
   no  : ¬ P → Dec P

reachable :  { V : Set } ( E : V → V → Set ) ( x y : V ) → Set
reachable {V} E x y = Dec ( connected {V} E x y )

dag :  { V : Set } ( E : V → V → Set ) →  Set
dag {V} E =  ∀ (n : V)  →  ¬ ( connected E n n )

-- dag {V} E =  ∀ (n : V)  →   connected E n n → ⊥

lemma4 : dag TwoArrow
lemma4 = {!   !}

lemma5 :  ¬ ( dag Circle )
lemma5 x = x t0 lemma3

-- record Finite ( A : Set ) : Set where
--    field
--       a : ?
-- 
-- record FiniteE {A : Set} ( E : A → A → Set ) : Set where
--    field
--       a : ?
-- 
-- lemma6 : ( V : Set ) ( E : V → V → Set ) → Finite V → FiniteE E → ( x y : V ) → reachable E x y
-- lemma6 = ?
-- 
--