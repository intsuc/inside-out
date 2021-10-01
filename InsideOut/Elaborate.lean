import InsideOut.Syntax
import InsideOut.Error

abbrev Ctx := List (String × Typ)
abbrev App := List Typ

abbrev M := Except Error

mutual

partial def checkOutsideIn (Γ : Ctx) : Exp → Typ → M Typ
  | exp let x₁ ∷ t₂ ≔ e₃; e₄, t => do
    let t₃ ← checkOutsideIn Γ e₃ t₂
    checkOutsideIn ((x₁, t₃) :: Γ) e₄ t

  | exp e@(exp abs x₁ ⇒ e₂), typ ? ⇒ t₂ => do
    let (t₂, Γ) ← checkInsideOut Γ e₂ t₂
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => typ t₁ ⇒ t₂
    | none         => throw $ Error.partialInferenceFailure e s!"? ⇒ {t₂}"

  | exp abs x₁ ⇒ e₂, typ t₁ ⇒ t₂ => do
    let t₂ ← checkOutsideIn ((x₁, t₁) :: Γ) e₂ t₂
    typ t₁ ⇒ t₂

  | exp iff e₁ then e₂ else e₃, t => do
    let _  ← checkOutsideIn Γ e₁ $ typ bool
    let t₂ ← checkOutsideIn Γ e₂ t
    checkOutsideIn Γ e₃ t₂

  | e, typ ? => inferOutsideIn Γ [] e

  | e, expected => do
    let found ← inferOutsideIn Γ [] e
    if expected == found then found else throw $ Error.typeMismatch s!"{expected}" s!"{found}"

partial def inferOutsideIn (Γ : Ctx) : App → Exp → M Typ
  | Ψ, exp let x₁ ∷ t₂ ≔ e₃; e₄ => do
    let t₃ ← checkOutsideIn Γ e₃ t₂
    inferOutsideIn ((x₁, t₃) :: Γ) Ψ e₄

  | _, e@(exp #x₁) =>
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => t₁
    | none         => throw $ Error.unknownVariable x₁

  | [], e@(exp abs x₁ ⇒ e₂) => do
    let (t₂, Γ) ← inferInsideOut Γ e₂
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => typ t₁ ⇒ t₂
    | none         => throw $ Error.partialInferenceFailure e s!"? ⇒ {t₂}"

  | t₁ :: Ψ, e@(exp abs x₁ ⇒ e₂) => do
    let t₂ ← inferOutsideIn ((x₁, t₁) :: Γ) Ψ e₂
    typ t₁ ⇒ t₂

  | Ψ, exp e₁ ◁ e₂ => do
    let t₂ ← inferOutsideIn Γ [] e₂
    let t₁ ← inferOutsideIn Γ (t₂ :: Ψ) e₁
    match t₁ with
    | typ _ ⇒ t₁₂ => t₁₂
    | found       => throw $ Error.typeMismatch "_ ⇒ _" s!"{found}"

  | [], exp ff => typ bool

  | [], exp tt => typ bool

  | Ψ, exp iff e₁ then e₂ else e₃ => do
    let _ ← checkOutsideIn Γ e₁ $ typ bool
    let t₂ ← inferOutsideIn Γ Ψ e₂
    checkOutsideIn Γ e₃ t₂

  | _, exp e₁ ∷ t₂ => checkOutsideIn Γ e₁ t₂

  | _, e => throw $ Error.inferenceFailure e

partial def checkInsideOut (Γ : Ctx) : Exp → Typ → M (Typ × Ctx)
  | exp let x₁ ∷ t₂ ≔ e₃; e₄, t => do
    let (t₃, Γ) ← checkInsideOut Γ e₃ t₂
    checkInsideOut ((x₁, t₃) :: Γ) e₄ t

  | exp #x₁, t => (t, (x₁, t) :: Γ)

  | exp abs x₁ ⇒ e₂, typ t₁ ⇒ t₂ => do
    let (t₂, Γ) ← checkInsideOut ((x₁, t₁) :: Γ) e₂ t₂
    (typ t₁ ⇒ t₂, Γ)

  | exp iff e₁ then e₂ else e₃, t => do
    let (_,  Γ) ← checkInsideOut Γ e₁ $ typ bool
    let (t₂, Γ) ← checkInsideOut Γ e₂ t
    checkInsideOut Γ e₃ t₂

  | e, typ ? => inferInsideOut Γ e

  | e, expected => do
    let (found, Γ) ← inferInsideOut Γ e
    if expected == found then (found, Γ) else throw $ Error.typeMismatch s!"{expected}" s!"{found}"

partial def inferInsideOut (Γ : Ctx) : Exp → M (Typ × Ctx)
  | exp let x₁ ∷ t₂ ≔ e₃; e₄ => do
    let (t₃, Γ) ← checkInsideOut Γ e₃ t₂
    inferInsideOut ((x₁, t₃) :: Γ) e₄

  | e@(exp #x₁) =>
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => (t₁, Γ)
    | none         => throw $ Error.inferenceFailure e

  | e@(exp abs x₁ ⇒ e₂) => do
    let (t₂, Γ) ← inferInsideOut Γ e₂
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => (typ t₁ ⇒ t₂, Γ)
    | none         => throw $ Error.partialInferenceFailure e s!"? ⇒ {t₂}"

  | exp e₁ ◁ e₂ => do
    let (t₁, Γ) ← inferInsideOut Γ e₁
    match t₁ with
    | typ t₁₁ ⇒ t₁₂ =>
      let (_, Γ) ← checkInsideOut Γ e₂ t₁₁
      (t₁₂, Γ)
    | found => throw $ Error.typeMismatch "_ ⇒ _" s!"{found}"

  | exp ff => (typ bool, Γ)

  | exp tt => (typ bool, Γ)

  | exp iff e₁ then e₂ else e₃ => do
    let (_,  Γ) ← checkInsideOut Γ e₁ $ typ bool
    let (t₂, Γ) ← inferInsideOut Γ e₂
    checkInsideOut Γ e₃ t₂

  | exp e₁ ∷ t₂ => checkInsideOut Γ e₁ t₂

end
