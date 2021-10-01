import InsideOut.Syntax

inductive Error where
  | unknownVariable         : (name : String) → Error
  | typeMismatch            : (expected : String) → (found : String) → Error
  | partialInferenceFailure : Exp → (found : String) → Error
  | inferenceFailure        : Exp → Error

instance : ToString Error where
  toString
    | Error.unknownVariable name            => s!"unknown variable '#{name}'"
    | Error.typeMismatch expected found     => s!"type expected '{expected}'; found '{found}'"
    | Error.partialInferenceFailure e found => s!"partially failed to infer '{e} ∷ {found}'"
    | Error.inferenceFailure e              => s!"failed to infer '{e}'"
