import InsideOut.Syntax

abbrev Ctx := Array (String × Typ)

abbrev M := Except String

mutual

partial def checkOutsideIn (Γ : Ctx) : Exp → Typ → M Unit
  | exp let x₁ ∷ t₂ ≔ e₃; e₄, t => do
    checkOutsideIn Γ e₃ t₂
    checkOutsideIn (Γ.push (x₁, t₂)) e₄ t

  | exp abs x₁ ⇒ e₂, typ t₁ ⇒ t₂ => do
    checkOutsideIn (Γ.push (x₁, t₁)) e₂ t₂

  | exp iff e₁ then e₂ else e₃, t => do
    checkOutsideIn Γ e₁ $ typ bool
    checkOutsideIn Γ e₂ t
    checkOutsideIn Γ e₃ t

  | e, expected => do
    let found ← inferOutsideIn Γ e
    if expected == found then () else throw s!"type expected '{expected}'; found '{found}'"

partial def inferOutsideIn (Γ : Ctx) : Exp → M Typ
  | exp let x₁ ∷ t₂ ≔ e₃; e₄ => do
    checkOutsideIn Γ e₃ t₂
    inferOutsideIn (Γ.push (x₁, t₂)) e₄

  | e@(exp #x₁) =>
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => t₁
    | none         => throw s!"unknown variable '{e}'"

  | e@(exp abs x₁ ⇒ e₂) => do
    let (t₂, Γ) ← inferInsideOut Γ e₂
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => typ t₁ ⇒ t₂
    | none         => throw s!"partially failed to infer '{e} ∷ ? ⇒ {t₂}'"

  | exp e₁ ◁ e₂ => do
    let t₁ ← inferOutsideIn Γ e₁
    match t₁ with
    | typ t₁₁ ⇒ t₁₂ =>
      checkOutsideIn Γ e₂ t₁₁
      t₁₂
    | found => throw s!"type expected '_ ⇒ _'; found '{found}'"

  | exp ff => typ bool

  | exp tt => typ bool

  | exp iff e₁ then e₂ else e₃ => do
    checkOutsideIn Γ e₁ $ typ bool
    let t₂ ← inferOutsideIn Γ e₂
    checkOutsideIn Γ e₃ t₂
    t₂

  | exp e₁ ∷ t₂ => do
    checkOutsideIn Γ e₁ t₂
    t₂

partial def checkInsideOut (Γ : Ctx) : Exp → Typ → M Ctx
  | exp let x₁ ∷ t₂ ≔ e₃; e₄, t => do
    let Γ ← checkInsideOut Γ e₃ t₂
    checkInsideOut (Γ.push (x₁, t₂)) e₄ t

  | exp #x₁, t => Γ.push (x₁, t)

  | exp abs x₁ ⇒ e₂, typ t₁ ⇒ t₂ => do
    checkInsideOut (Γ.push (x₁, t₁)) e₂ t₂

  | exp iff e₁ then e₂ else e₃, t => do
    let Γ ← checkInsideOut Γ e₁ $ typ bool
    let Γ ← checkInsideOut Γ e₂ t
    checkInsideOut Γ e₃ t

  | e, expected => do
    let (found, Γ) ← inferInsideOut Γ e
    if expected == found then Γ else throw s!"type expected '{expected}'; found '{found}'"

partial def inferInsideOut (Γ : Ctx) : Exp → M (Typ × Ctx)
  | exp let x₁ ∷ t₂ ≔ e₃; e₄ => do
    let Γ ← checkInsideOut Γ e₃ t₂
    inferInsideOut (Γ.push (x₁, t₂)) e₄

  | e@(exp #x₁) =>
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => (t₁, Γ)
    | none         => throw s!"failed to infer '{e}'"

  | e@(exp abs x₁ ⇒ e₂) => do
    let (t₂, Γ) ← inferInsideOut Γ e₂
    match Γ.find? (·.1 == x₁) with
    | some (_, t₁) => (typ t₁ ⇒ t₂, Γ)
    | none         => throw s!"partially failed to infer '{e} ∷ ? ⇒ {t₂}'"

  | exp e₁ ◁ e₂ => do
    let (t₁, Γ) ← inferInsideOut Γ e₁
    match t₁ with
    | typ t₁₁ ⇒ t₁₂ =>
      let Γ ← checkInsideOut Γ e₂ t₁₁
      (t₁₂, Γ)
    | found => throw s!"type expected '_ ⇒ _'; found '{found}'"

  | exp ff => (typ bool, Γ)

  | exp tt => (typ bool, Γ)

  | exp iff e₁ then e₂ else e₃ => do
    let Γ       ← checkInsideOut Γ e₁ $ typ bool
    let (t₂, Γ) ← inferInsideOut Γ e₂
    let Γ       ← checkInsideOut Γ e₃ t₂
    (t₂, Γ)

  | exp e₁ ∷ t₂ => do
    let Γ ← checkInsideOut Γ e₁ t₂
    (t₂, Γ)

end
