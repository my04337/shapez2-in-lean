# Copilot Instructions - Shapez2 in Lean

## 応答言語
- 日本語で応答する

## プロジェクト概要
- **正式名称**: Shapez2 in Lean（略称: **S2IL**）

## 参照ドキュメント一覧

エージェントは推論時に必要に応じて以下を参照すること。

### Shapez2 ゲーム用語
| ファイル | 内容 |
|---|---|
| `docs/shapez2/glossary.md` | ゲーム内用語集（シェイプ・建物・操作など） |
| `docs/shapez2/adjacency.md` | 隣接関係の定義（同レイヤ内・上下レイヤ間・東西分類） |
| `docs/shapez2/crystal-shatter.md` | 結晶の砕け散りに関する仕様と実装方針 |

### Lean 4 ・数学
| ファイル | 内容 |
|---|---|
| `docs/lean/lean-reference-guide.md` | Lean 4 言語仕様リファレンスの索引（文法・型・タクティクなど） |
| `docs/lean/theorem-proving-guide.md` | 定理証明の実践ガイド（タクティク・帰納型・再帰など） |
| `docs/lean/fp-in-lean-guide.md` | 関数型プログラミング in Lean ガイド |
| `docs/lean/math-glossary.md` | 数学用語辞書（型理論・論理学・代数構造など） |
| `docs/lean/toolchain-guide.md` | ツールチェインガイド（elan・Lake・Lean 等の役割） |

### プロジェクト固有のナレッジ

証明やコーディングで行き詰まった場合、まず以下を参照すること。
過去の試行錯誤から得られた実践的なパターンと回避策がまとまっている。

| ファイル | 内容 |
|---|---|
| `docs/knowledge/lean-proof-tips.md` | Lean 4 証明の実践 Tips（タクティク使い分け・`List.mapM` 回避など） |
| `docs/knowledge/string-roundtrip-proof.md` | 文字列ラウンドトリップ定理の証明パターン（`String` 展開不可問題の回避策） |

## コーディング規約
- 文字コード: UTF-8 (BOMなし)。ただしBOMが必要な場合はBOMを付ける
- 改行コード: CRLF
- コメントは日本語で記述
- インデント: スペース4つ
- 新規ファイルには以下の SPDX ヘッダを追加
  ```lean
  -- SPDX-FileCopyrightText: <作成年> my04337
  -- SPDX-License-Identifier: MIT
  ```
  - 新規作成: `<作成年>` = 現在の年（例: 2026）
  - 大幅改変: 範囲表記に更新（例: 2018-2026）
  - 既存ファイルに SPDX ヘッダが無い場合、追加しない

## Lean 4 命名規則

> 参考: [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html),
> [Library style guidelines](https://leanprover-community.github.io/contribute/style.html)

### 基本ルール（大文字・小文字の使い分け）

命名規則は**宣言の返り値の型**で決まる。

| 分類 | ケース | 対象 | 例 |
|---|---|---|---|
| `Prop` の項（証明） | `snake_case` | 定理・補題・証明 | `add_comm`, `zero_add`, `succ_ne_zero`, `mul_pos` |
| `Prop` / `Type` / `Sort` 自体 | `UpperCamelCase` | 帰納型・構造体・クラス | `Nat`, `List`, `OneHom`, `HPow` |
| 上記以外の `Type` の項 | `lowerCamelCase` | 関数・定義・値 | `toString`, `getSize`, `List.map` |

関数は**返り値の型**に従って命名する:
- `A → B → Prop` を返す関数（定理として使える） → `snake_case`（例: `lt_of_succ_le`）
- `A → Type` を返す関数（型構築） → `UpperCamelCase`（例: `CategoryTheory.Functor`）
- `A → B` で `B` が `Type` の項 → `lowerCamelCase`（例: `List.length`, `toString`）

### 名前空間・ファイル名

- 名前空間: `UpperCamelCase`（例: `Nat`, `List`, `S2IL`）
- `.lean` ファイル名: `UpperCamelCase`（例: `Basic.lean`, `NatColor.lean`）

### 略語（アクロニム）の扱い

略語はケースに応じてグループ単位で大文字・小文字にする。単語の途中で大文字小文字を混ぜない。

| ケース | 例 |
|---|---|
| `UpperCamelCase` 中 | `HPow`, `LT`, `LE`, `IO` |
| `lowerCamelCase` 中 | `hPow`, `lt`, `le`, `io` |
| `snake_case` 中 | `h_pow`, `lt_iff_le`, `io_bind` |

### 構造体フィールド・コンストラクタ

フィールドやコンストラクタも上記の基本ルールに従う。

```lean
structure OneHom (M : Type) (N : Type) [One M] [One N] where
    toFun : M → N                -- lowerCamelCase（Type の項）
    map_one' : toFun 1 = 1       -- snake_case（Prop の項 = 証明義務）
```

### ドット記法と名前空間

- 型名を名前空間として関数を定義し、ドット記法で呼び出す
  ```lean
  def List.map (f : α → β) : List α → List β := ...
  #eval [1, 2, 3].map (· + 1)
  ```
- 論理結合子のイントロ・エリム等もドット記法を活用する
  - `And.intro`, `And.left`, `Or.inl`, `Eq.symm`, `Eq.trans` など

### Prop-valued クラス（述語クラス）の命名

- 名詞の場合: `Is` 接頭辞を付ける（例: `IsTopologicalRing`, `IsEmpty`）
- 形容詞の場合: `Is` 接頭辞は不要（例: `Normal`, `Finite`）
- 述語関数: `is` / `has` 接頭辞を使用（例: `isEven`, `hasDecEq`）

### 定理名の説明的命名パターン

定理名は基本的に**結論を描写**する。仮定の記述が必要な場合は `_of_` で区切る。

| パターン | 例 | 意味 |
|---|---|---|
| 結論をそのまま | `mul_zero`, `succ_ne_zero` | `a * 0 = 0`, `succ n ≠ 0` |
| `_of_` で仮定記述 | `lt_of_succ_le`, `lt_of_le_of_ne` | 仮定の順に列挙 |
| `_left` / `_right` | `add_le_add_left` | 左右の変形 |
| 省略形 | `pos`, `neg`, `nonpos`, `nonneg` | `0 < x`, `x < 0`, `x ≤ 0`, `0 ≤ x` |
| 公理的性質 | `refl`, `symm`, `trans`, `comm`, `assoc` | 反射・対称・推移・交換・結合 |

### `UpperCamelCase` を `snake_case` 中で参照する場合

`UpperCamelCase` の名前が `snake_case` の定理名中に現れるときは `lowerCamelCase` に変換する。

```lean
-- MonoidHom → monoidHom, OneHom → oneHom
theorem MonoidHom.toOneHom_injective : ...
-- Nat.cast → natCast
theorem map_natCast : ...
```

### 変数名の慣例

| 変数 | 用途 |
|---|---|
| `u`, `v`, `w` | 宇宙レベル |
| `α`, `β`, `γ` | 汎用的な型 |
| `x`, `y`, `z` | 汎用型の要素 |
| `h`, `h₁`, `h₂` | 仮定・仮説 |
| `p`, `q`, `r` | 述語・関係 |
| `m`, `n`, `k` | 自然数 |
| `i`, `j`, `k` | 整数 |
| `s`, `t` | リスト・集合 |
| `f`, `g` | 関数 |

## 外部ライブラリのライセンス方針
- **利用可**: パブリックドメイン、MIT-0 等（義務なし）
- **要確認**: MIT, BSD-2, BSD-3, MPL 2.0 等（著作権・許諾表示が必要）
- **利用厳禁**: GPL, AGPL, LGPL 等コピーレフト系、商用ライブラリ、ライセンス不明・制限が厳しいもの
