module automaton.4_1 where
record NAutomaton (Q Σ : Set) : Set where
  field
    δ       : Q → Σ → List Q      -- 遷移関数: 現在の状態とシンボルから次の状態のリスト
    all-states : List Q           -- すべての状態
    exists  : (Q → Bool) → Bool   -- 存在量化の補助関数
    Nstart  : Q → Bool            -- 開始状態の判定

NNtrace : {Q Σ : Set} →
          NAutomaton Q Σ →
          List Q →                -- 全状態のリスト
          (Q → Bool) →            -- 存在判定の関数
          (Q → Bool) →            -- 開始状態の判定
          List Σ →                -- 入力シンボルのリスト
          ℕ →                     -- ステップ数
          List Q                  -- 到達可能な状態のリスト
NNtrace {Q} {Σ} automaton all-states exists Nstart [] 0 = 
  filter Nstart all-states       -- 初期状態をリストで返す
NNtrace {Q} {Σ} automaton all-states exists Nstart [] (suc n) =
  []
NNtrace {Q} {Σ} automaton all-states exists Nstart (x ∷ xs) 0 = 
  filter Nstart all-states
NNtrace {Q} {Σ} automaton all-states exists Nstart (x ∷ xs) (suc n) =
  let δ = NAutomaton.δ automaton in
  let current-states = NNtrace automaton all-states exists Nstart (x ∷ xs) n in
  let next-states = concatMap (λ q → δ q x) current-states in
  filter (`elem` all-states) next-states
