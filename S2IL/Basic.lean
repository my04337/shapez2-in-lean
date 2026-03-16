-- プレースホルダー: 今後 Shapez2 のロジックをここに実装していく

/-- プロジェクト名 -/
def projectName : String := "Shapez2 in Lean"

/-- 色の種類 (プレースホルダー) -/
inductive Color where
  | red | green | blue | yellow
  deriving Repr, DecidableEq

/-- 同じ色は等しい (プレースホルダー定理) -/
theorem colorRefl (c : Color) : c = c := rfl
