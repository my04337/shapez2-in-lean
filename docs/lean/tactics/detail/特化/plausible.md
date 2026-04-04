# `plausible` — ランダムテストによる反例探索

**カテゴリ**: 特化 | **定義元**: `plausibleSyntax` | **ソース**: Mathlib/Std

> **⚠️ 実験的ツール**: `plausible` はテスト・デバッグ用途のタクティクであり、最終的な証明には使用しないこと。全テストをパスしても命題の真偽を保証するものではない。

## 概要
`plausible` は QuickCheck スタイルのランダムテストを実行し、命題の反例を探索するタクティク。`∀` で量化された命題に対してランダムな入力を生成し、反例が見つかった場合はその具体値を報告する。全テストをパスした場合はゴールを `sorry` で閉じる（`admit` 扱い）。証明の事前検証や仮説チェックに有用。

## ゴールパターン

**適用前**
```lean
⊢ ∀ n : Nat, n + n = 2 * n
```

**適用後**（反例なし）: ゴールが `sorry` で閉じる（admit）

**適用後**（反例あり）: 反例の具体値がエラーとして報告される

## 構文
```lean
plausible              -- デフォルト設定でランダムテスト
plausible (config := { numInst := 1000 })  -- テスト数を指定
```

## 必須 import
```lean
import Mathlib.Tactic.Plausible   -- または import Plausible
```

## オプション一覧
| 構文 | 意味 |
|---|---|
| `plausible` | デフォルト（100回テスト） |
| `(config := { numInst := n })` | テスト回数を n に設定 |
| `(config := { randomSeed := s })` | 乱数シードを指定（再現性） |

## Pros
- 偽命題の早期発見に非常に有効
- 反例を具体値で報告するためデバッグしやすい
- `Testable` インスタンスがあれば任意の型に適用可能
- 証明に着手する前の仮説検証に最適

## Cons
- **証明ではない**: 全テストをパスしても `sorry` が残る
- ランダムテストのため、稀なケースの反例を見逃す可能性がある
- `Testable` / `Sampleable` インスタンスが必要
- 複雑な型（高階関数、依存型等）ではテスト生成が困難
- 最終的な証明コードには残してはいけない

## コードサンプル

### サンプル 1: 正しい命題の検証
```lean
import Plausible

-- 反例なし → sorry で閉じる（最終証明では omega 等に置き換えること）
example : ∀ n : Nat, n + 0 = n := by
  plausible
  -- ✅ 100 テストをパス（sorry で閉じる）
```

### サンプル 2: 偽命題の反例発見
```lean
import Plausible

-- 注: plausible は反例を発見するとエラーを場出する（コンパイル中止）
-- example : ∀ n : Nat, n < 10 := by plausible  -- ← n := 10 を反例として報告
```

### サンプル 3: テスト回数を増やして検証
```lean
import Plausible

example : ∀ (a b : Nat), a + b = b + a := by
  plausible (config := { numInst := 500 })
  -- ✅ 500 テストをパス（sorry で閉じる）
  -- 最終証明では `intro a b; omega` に置き換えること
```

## 使い方のガイドライン

1. **証明着手前の仮説検証**: 補題が本当に成り立つか `plausible` で事前チェック
2. **偽命題の早期棄却**: 反例が見つかれば証明を試みる必要がない
3. **最終コードからの除去**: `plausible` は必ず正式な証明に置き換える
4. **CI では使わない**: `sorry` が残るため、CI の `sorry` チェックに引っかかる

## 関連タクティク
| タクティク | 関係 | 使い分け |
|---|---|---|
| `decide` | 決定手続き | Decidable なら完全に証明する |
| `omega` | 線形算術 | Nat/Int 算術の完全証明 |
| `norm_num` | 数値正規化 | 具体的な数値計算の証明 |
| `sorry` | 仮証明 | 手動でゴールをスキップ |

## 参照
- [Mathlib4 ドキュメント — Plausible](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Plausible.html)

---
> **出典**: [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/), [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
> 本ページは上記ドキュメントの情報を基に構成しています（Apache 2.0 License）。
