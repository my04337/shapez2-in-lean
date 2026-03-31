# Copilot Instructions - Shapez2 in Lean

## 応答言語
- 日本語で応答する

## プロジェクト概要
- **正式名称**: Shapez2 in Lean（略称: **S2IL**）

## 参照ドキュメント

エージェントは作業開始前に、作業カテゴリに対応する README.md を読み、適切なドキュメントを参照すること。

| カテゴリ | 入口 | 参照タイミング |
|---|---|---|
| Shapez2 ゲームドメイン | [`docs/shapez2/README.md`](../docs/shapez2/README.md) | ゲーム仕様の確認・実装・リファクタリング時 |
| Lean 4・数学 | [`docs/lean/README.md`](../docs/lean/README.md) | Lean 構文・証明戦略・Mathlib 利用時 |
| 証明ナレッジ | [`docs/knowledge/README.md`](../docs/knowledge/README.md) | 証明着手前・行き詰まった時・knowledge 更新時 |
| 計画・マイルストーン | [`docs/plans/README.md`](../docs/plans/README.md) | マイルストーン更新・証明計画策定時 |
| エージェントカスタマイズ | [`docs/agent/README.md`](../docs/agent/README.md) | Skills / Hooks 設定の追加・変更時 |

### 作業別のナビゲーション

| 作業 | 参照フロー |
|---|---|
| 新しい証明に着手 | knowledge → lean → 対象の仕様ドキュメント |
| ゲーム仕様の実装・変更 | shapez2 → knowledge |
| マイルストーン・計画の更新 | plans |
| 考察・ナレッジの追記 | 対象カテゴリの README.md の編集ガイダンスに従う |
| リファクタリング | knowledge → shapez2（仕様の再確認） |

## コーディング規約

### 基本規約
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

### Lean 4 命名規則

> 参考: [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html),
> [Library style guidelines](https://leanprover-community.github.io/contribute/style.html)

#### 基本ルール（大文字・小文字の使い分け）

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

#### 名前空間・ファイル名

- 名前空間: `UpperCamelCase`（例: `Nat`, `List`, `S2IL`）
- `.lean` ファイル名: `UpperCamelCase`（例: `Basic.lean`, `NatColor.lean`）

#### 略語（アクロニム）の扱い

略語はケースに応じてグループ単位で大文字・小文字にする。単語の途中で大文字小文字を混ぜない。

| ケース | 例 |
|---|---|
| `UpperCamelCase` 中 | `HPow`, `LT`, `LE`, `IO` |
| `lowerCamelCase` 中 | `hPow`, `lt`, `le`, `io` |
| `snake_case` 中 | `h_pow`, `lt_iff_le`, `io_bind` |

#### 構造体フィールド・コンストラクタ

フィールドやコンストラクタも上記の基本ルールに従う。

```lean
structure OneHom (M : Type) (N : Type) [One M] [One N] where
    toFun : M → N                -- lowerCamelCase（Type の項）
    map_one' : toFun 1 = 1       -- snake_case（Prop の項 = 証明義務）
```

#### ドット記法と名前空間

- 型名を名前空間として関数を定義し、ドット記法で呼び出す
  ```lean
  def List.map (f : α → β) : List α → List β := ...
  #eval [1, 2, 3].map (· + 1)
  ```
- 論理結合子のイントロ・エリム等もドット記法を活用する
  - `And.intro`, `And.left`, `Or.inl`, `Eq.symm`, `Eq.trans` など

#### Prop-valued クラス（述語クラス）の命名

- 名詞の場合: `Is` 接頭辞を付ける（例: `IsTopologicalRing`, `IsEmpty`）
- 形容詞の場合: `Is` 接頭辞は不要（例: `Normal`, `Finite`）
- 述語関数: `is` / `has` 接頭辞を使用（例: `isEven`, `hasDecEq`）

#### 定理名の説明的命名パターン

定理名は基本的に**結論を描写**する。仮定の記述が必要な場合は `_of_` で区切る。

| パターン | 例 | 意味 |
|---|---|---|
| 結論をそのまま | `mul_zero`, `succ_ne_zero` | `a * 0 = 0`, `succ n ≠ 0` |
| `_of_` で仮定記述 | `lt_of_succ_le`, `lt_of_le_of_ne` | 仮定の順に列挙 |
| `_left` / `_right` | `add_le_add_left` | 左右の変形 |
| 省略形 | `pos`, `neg`, `nonpos`, `nonneg` | `0 < x`, `x < 0`, `x ≤ 0`, `0 ≤ x` |
| 公理的性質 | `refl`, `symm`, `trans`, `comm`, `assoc` | 反射・対称・推移・交換・結合 |

#### `UpperCamelCase` を `snake_case` 中で参照する場合

`UpperCamelCase` の名前が `snake_case` の定理名中に現れるときは `lowerCamelCase` に変換する。

```lean
-- MonoidHom → monoidHom, OneHom → oneHom
theorem MonoidHom.toOneHom_injective : ...
-- Nat.cast → natCast
theorem map_natCast : ...
```

#### 変数名の慣例

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

### 外部ライブラリのライセンス方針
- **利用可**: パブリックドメイン、MIT-0 等（義務なし）
- **要確認**: MIT, BSD-2, BSD-3, MPL 2.0 等（著作権・許諾表示が必要）
- **利用厳禁**: GPL, AGPL, LGPL 等コピーレフト系、商用ライブラリ、ライセンス不明・制限が厳しいもの

## GameConfig（ゲーム設定）の設計方針

`GameConfig` は**構造体**であり、レイヤ数上限を必要とする関数には**明示的に引数として渡す**。
型クラス (`class`) やデフォルト引数 (`inferInstance`) は使用しない。

```lean
-- ✅ 正しい使い方: 明示的に config を渡す
Shape.stack bottom top GameConfig.vanilla4
s.pinPush GameConfig.vanilla5

-- ❌ 避けるべき使い方: デフォルト引数に頼る
Shape.stack bottom top  -- config を省略しない
```

### プリセット

| 定義 | レイヤ数 | 用途 |
|---|---|---|
| `GameConfig.vanilla4` | 4 | 通常モード (Normal / Hard) |
| `GameConfig.vanilla5` | 5 | 高難度モード (Insane) |
| `GameConfig.stress16` | 16 | ストレステスト専用 |

カスタム設定は `GameConfig.mk n proof` で自由に構築できる。

## テスト方針

### GameConfig ごとのテストレベル

| レベル | 対象 config | 方針 |
|---|---|---|
| **標準テスト** | `vanilla4`, `vanilla5` | 全操作で網羅的にテスト |
| **ストレステスト** | 16レイヤ等の大規模 config | ボトルネック性質（truncate 冪等性等）のみ |

- テストヘルパーには使用する `GameConfig` を明示する（例: `stackTest` は vanilla4 使用）
- 16レイヤ等のストレステストは `Test/Shape/Shape.lean` に配置し、層ごとの力業 (`cases`) が不可能な規模で性質を検証する

## 動作環境・シェル

### 各プラットフォームで想定するシェル

| OS | シェル | 備考 |
|---|---|---|
| Windows | PowerShell 7 | 最低でもプリインストールの PowerShell 5 以上 |
| macOS | zsh | 一般的なモダンシェルで動作可能 |
| Linux | bash | 一般的なモダンシェルで動作可能 |

### スクリプト実行規則

`.github/skills/` 配下のスクリプトを実行する際は、**シェル名を前置せず直接実行すること**。

```
# ✅ 正しい実行方法（直接実行）
.github/skills/lean-build/scripts/build.ps1
.github/skills/lean-build/scripts/build.sh

# ❌ 避けるべき実行方法（シェル明示）
pwsh.exe -File .github/skills/lean-build/scripts/build.ps1
bash .github/skills/lean-build/scripts/build.sh
```

- Windows: `.ps1` ファイルは PowerShell で自動的に実行される
- macOS / Linux: `.sh` ファイルは shebang (`#!/usr/bin/env bash`) により適切なシェルで実行される
  - 初回実行時に `chmod +x` が必要な場合がある
