module Control.Effect.Algebraic.Free
  where

open import Agda.Primitive
  using
    ( _⊔_
    )
  renaming
    ( lsuc to ℓsuc
    ; lzero to 0ℓ
    )

open import Foundations.Base

open import Control.Effect.Algebraic.Effect
  using
    ( Effect
    ; _⊕_
    ; _∈_; ~; -∷_; ~∷-
    ; inject; project
    )

open Effect


data Free {o r ℓ : Level} (Eff : Effect o r) (A : Type ℓ) : Type (o ⊔ r ⊔ ℓ) where
  pure
    : (a : A)
    → Free Eff A
  impure
    : (op : Op Eff)
    → (k : Ret Eff op → Free Eff A)
    → Free Eff A

Alg
  : {o r a : Level}
  → (Eff : Effect o r)
  → (A : Type a)
  → Type (o ⊔ r ⊔ a)
Alg Eff A = (op : Op Eff) → (k : Ret Eff op → A) → A

fold
  : {o r a b : Level}
  → {Eff : Effect o r} {A : Type a} {B : Type b}
  → (A → B)
  → (Alg Eff B)
  → Free Eff A
  → B
fold point alg (pure a) = point a
fold point alg (impure op k) = alg op (λ r → fold point alg (k r))

_>>=_
  : {o r a b : Level}
  → {Eff : Effect o r} {A : Type a} {B : Type b}
  → Free Eff A
  → (A → Free Eff B)
  → Free Eff B
f >>= g = fold g impure f

_>>_
  : {o r a b : Level}
  → {Eff : Effect o r} {A : Type a} {B : Type b}
  → Free Eff A
  → Free Eff B
  → Free Eff B
f >> g = f >>= λ _ → g

send
  : {o r : Level}
  → {Eff : Effect o r} {Effs : Effect o r}
  → ⦃ Eff∈Effs : Eff ∈ Effs ⦄
  → (op : Op Eff)
  → Free Effs (Ret Eff op)
send ⦃ Eff∈Effs = Eff∈Effs ⦄ op = impure (inject Eff∈Effs op) λ ret → pure (project Eff∈Effs ret)


-----------------------------------------------------
Pure : Effect 0ℓ 0ℓ
Pure = record
  { Op = ⊥
  ; Ret = λ ()
  }

runPure
  : {a : Level} {A : Type a}
  → Free Pure A
  → A
runPure =
  fold
    (λ x → x)
    (λ ())

-----------------------------------------------------
data ReaderOp {e : Level} (E : Type e) : Type e where
  ask : ReaderOp E

Reader : {e : Level} (E : Type e) → Effect e e
Reader E = record
  { Op = ReaderOp E
  ; Ret = λ where
      ask → E
  }

runReader
  : {e a : Level} {E : Type e} {Effs : Effect e e} {A : Type a}
  → Free (Reader E ⊕ Effs) A
  → E
  → Free Effs A
runReader =
  fold
    (λ a e → pure a )
    (λ where
      (inl ask) k e → k e e
      (inr op) k e → impure op λ ret → k ret e
    )

-----------------------------------------------------
data StateOp {s : Level} (S : Type s) : Type s where
  modify : (S → S) → StateOp S

State : {s : Level} (S : Type s) → Effect s s
State S = record
  { Op = StateOp S
  ; Ret = λ where
      (modify _) → S
  }


runState
  : {s a : Level} {S : Type s} {Effs : Effect s s} {A : Type a}
  → Free (State S ⊕ Effs) A
  → S
  → Free Effs (S × A)
runState =
  fold
    (λ a s → pure (s , a) )
    (λ where
      (inl (modify f)) k s → k (f s) (f s)
      (inr op) k s → impure op λ ret → k ret s
    )


module Examples where

  module PureExample where
    program : Free Pure ⊤
    program = do
      pure tt

    -- _ : runPure program ＝ tt
    -- _ = ?

  module ReaderExample where
    program
      : {Effs : Effect 0ℓ 0ℓ}
      → ⦃ Reader ⊤ ∈ Effs ⦄
      → Free Effs ⊤
    program = do
      send ask

    -- _ : runPure (runReader program tt) ＝ tt
    -- _ = ?

  module StateExample where
    program
      : {Effs : Effect 0ℓ 0ℓ}
      → ⦃ State ⊤ ∈ Effs ⦄
      → Free Effs ⊤
    program = do
      send (modify λ x → x)

    -- _ : runPure (runState program tt) ＝ (tt , tt)
    -- _ = ?

  module ReaderStateExample where
    program
      : {Effs : Effect 0ℓ 0ℓ}
      → ⦃ Reader ⊤ ∈ Effs ⦄
      → ⦃ State ⊤ ∈ Effs ⦄
      → Free Effs ⊤
    program = do
      send ask
      send (modify λ x → x)

    -- _ : runPure (runState (runReader program tt) tt) ＝ (tt , tt)
    -- _ = ?
