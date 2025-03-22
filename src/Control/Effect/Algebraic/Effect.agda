module Control.Effect.Algebraic.Effect
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

record Effect (o r : Level) : Type (ℓsuc (o ⊔ r)) where
  field
    Op : Type o
    Ret : Op → Type r

open Effect

_⊕_
  : {oₗ oᵣ r : Level}
  → (effₗ : Effect oₗ r)
  → (effᵣ : Effect oᵣ r)
  → Effect (oₗ ⊔ oᵣ) r
effₗ ⊕ effᵣ = record
  { Op = Op effₗ ⊎ Op effᵣ
  ; Ret = λ where
      (inl opₗ) → Ret effₗ opₗ
      (inr opᵣ) → Ret effᵣ opᵣ
  }

infixr 5 _⊕_

data _∈_ {o r : Level} : (Effect o r) → (Effect o r) → Type (ℓsuc (o ⊔ r)) where
  ~
    : {eff : Effect o r}
    → eff ∈ eff
  ~∷-
    : {eff effs : Effect o r}
    → eff ∈ (eff ⊕ effs)
  -∷_
    : {eff eff′ effs : Effect o r}
    → (eff ∈ effs)
    → eff ∈ (eff′ ⊕ effs)

infix 4 _∈_


instance
  Effect-∈-here
    : {o r : Level}
    → {Eff : Effect o r}
    → Eff ∈ Eff
  Effect-∈-here = ~
  {-# OVERLAPS Effect-∈-here #-}

  Effect-∈-inl
    : {o r : Level}
    → {Eff : Effect o r} {Effs : Effect o r}
    → Eff ∈ Eff ⊕ Effs
  Effect-∈-inl = ~∷-
  {-# OVERLAPS Effect-∈-inl #-}

  Effect-∈-inr
    : {o r : Level}
    → {Eff′ Eff : Effect o r} {Effs : Effect o r}
    → ⦃ Eff∈Effs : Eff ∈ Effs ⦄
    → Eff ∈ Eff′ ⊕ Effs
  Effect-∈-inr ⦃ Eff∈Effs ⦄ = -∷ Eff∈Effs
  {-# OVERLAPS Effect-∈-inr #-}


inject
  : {o r : Level}
  → {Eff : Effect o r} {Effs : Effect o r}
  → (Eff ∈ Effs)
  → (op : Op Eff)
  → Op Effs
inject ~ op = op
inject ~∷- op = inl op
inject (-∷ p) op = inr (inject p op)

project
  : {o r : Level}
  → {Eff : Effect o r} {Effs : Effect o r}
  → (Eff∈Effs : Eff ∈ Effs)
  → {op : Op Eff}
  → (ret : Ret Effs (inject Eff∈Effs op))
  → Ret Eff op
project ~ ret = ret
project ~∷- ret = ret
project (-∷ i) ret = project i ret

module Examples where

  data Two : Type where
    one two : Two

  data Tri : Type where
    one two three : Tri

  Eff0 : Effect 0ℓ 0ℓ
  Eff0 .Op = ⊥
  Eff0 .Ret ()

  Eff1 : Effect 0ℓ 0ℓ
  Eff1 .Op = ⊤
  Eff1 .Ret tt = ⊥

  Eff2 : Effect 0ℓ 0ℓ
  Eff2 .Op = Two
  Eff2 .Ret _ = ⊤

  Eff3 : Effect 0ℓ 0ℓ
  Eff3 .Op = Tri
  Eff3 .Ret _ = Two

  _ : Eff0 ∈ Eff0
  _ = ~

  _ : Eff1 ∈ Eff1 ⊕ Eff0
  _ = ~∷-

  _ : Eff0 ∈ Eff1 ⊕ Eff0
  _ = -∷ ~

  _ : Eff1 ∈ Eff2 ⊕ Eff1 ⊕ Eff0
  _ = -∷ ~∷-
