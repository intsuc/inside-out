inductive Typ where
  | func : Typ → Typ → Typ
  | bool : Typ
  deriving Inhabited, BEq

inductive Exp where
  | «let» : String → Typ → Exp → Exp → Exp
  | var   : String → Exp
  | abs   : String → Exp → Exp
  | app   : Exp → Exp → Exp
  | ff    : Exp
  | tt    : Exp
  | iff   : Exp → Exp → Exp → Exp
  | anno  : Exp → Typ → Exp

declare_syntax_cat typ

declare_syntax_cat exp

syntax typ " ⇒ " typ : typ
syntax "bool"        : typ
syntax "( " typ " )" : typ
syntax term          : typ

syntax "let " term " ∷ " typ " ≔ " exp " ; " exp : exp
syntax:100 "# " term:100                         : exp
syntax "abs " term " ⇒ " exp                     : exp
syntax:65 exp:65 " ◁ " exp:66                    : exp
syntax "ff"                                      : exp
syntax "tt"                                      : exp
syntax "iff " exp " then " exp " else " exp      : exp
syntax exp " ∷ " typ                             : exp
syntax "( " exp " )"                             : exp
syntax term                                      : exp

macro_rules
  | `(typ| $t₁ ⇒ $t₂) => `(Typ.func $t₁ $t₂)
  | `(typ| bool)      => `(Typ.bool)
  | `(typ| ($t:typ))  => `(typ| $t)
  | `(typ| $t:term)   => t

macro_rules
  | `(exp| let $x₁ ∷ $t₂ ≔ $e₃; $e₄)  => `(Exp.let $x₁ $t₂ $e₃ $e₄)
  | `(exp| #$x₁)                      => `(Exp.var $x₁)
  | `(exp| abs $x₁ ⇒ $e₂)             => `(Exp.abs $x₁ $e₂)
  | `(exp| $e₁ ◁ $e₂)                 => `(Exp.app $e₁ $e₂)
  | `(exp| ff)                        => `(Exp.ff)
  | `(exp| tt)                        => `(Exp.tt)
  | `(exp| iff $e₁ then $e₂ else $e₃) => `(Exp.iff $e₁ $e₂ $e₃)
  | `(exp| $e₁ ∷ $t₂)                 => `(Exp.anno $e₁ $t₂)
  | `(exp| ($e:exp))                  => `(exp| $e)
  | `(exp| $e:term)                   => e

macro "typ " t:typ : term => t

macro "exp " e:exp : term => e

private def paren (p₁ p₂ : Nat) (s : String) : String :=
  if p₂ < p₁ then s!"({s})" else s

instance : ToString Typ where
  toString :=
    let rec go (p : Nat) : Typ → String
      | typ t₁ ⇒ t₂ => paren p 0 s!"{go 1 t₁} ⇒ {go 0 t₂}"
      | typ bool    => "bool"
    go 0

instance : ToString Exp where
  toString :=
    let rec go (p : Nat) : Exp → String
      | exp let x₁ ∷ t₂ ≔ e₃; e₄   => paren p 0 s!"let {x₁} ∷ {t₂} ≔ {go 0 e₃}; {go 0 e₄}"
      | exp #x₁                    => s!"#{x₁}"
      | exp abs x₁ ⇒ e₂            => paren p 0 s!"abs {x₁} ⇒ {go 0 e₂}"
      | exp e₁ ◁ e₂                => paren p 2 s!"{go 2 e₁} ◁ {go 3 e₂}"
      | exp ff                     => "ff"
      | exp tt                     => "tt"
      | exp iff e₁ then e₂ else e₃ => paren p 0 s!"iff {go 0 e₁} then {go 0 e₂} else {go 0 e₃}"
      | exp e₁ ∷ t₂                => paren p 1 s!"{go 1 e₁} ∷ {t₂}"
    go 0
