# 証明リファクタリング計画

> 対象: `S2IL/` 配下の全 `.lean` ファイル（`Gravity.lean` の `process_rotate180` 証明チェーンを除く）
> 作成日: 2026-04-05
> 最終更新: 2026-04-05

---

## 0. 背景・目的

プロジェクト初期に書かれた証明群は、Lean 4 への習熟度が低い状態で作成された。
結果として以下の技術的負債が蓄積している:

1. **裸 `simp` の多用**: Mathlib 更新で壊れうる不安定な証明
2. **証明の冗長性**: より強力なタクティクで短縮可能な証明が散在
3. **コメント・命名の不統一**: ファイル間でスタイルがバラバラ
4. **補題分割の不足**: 1 つの定理に 40-70 行の巨大証明が存在
5. **`@[simp]` 属性の設計不在**: 付与基準が不明確

加えて、設計判断の見直しも必要な箇所がある:

6. **早すぎるレイヤ数制約**: `Shape.stack` / `Shape.pinPush` に前提条件として入った `layerCount ≤ config.maxLayers` が、現段階では不要な複雑性を持ち込んでいる
7. **安定状態 (settled state) の考慮不足**: Machine の入出力が常に安定状態であるゲーム規定が、コード上で適切に表現されていない
8. **ドメインドキュメントの欠落**: `docs/shapez2/falling.md` に安定状態の説明がない等、仕様ドキュメントの改善余地がある

本計画では **Gravity.process_rotate180** のような進行中の新証明を除いた「枯れた証明」を対象に、
大胆なリファクタリングを行い、今後の証明作業の基盤品質を引き上げる。

---

## 1. 現状の定量分析

### 1.1 ファイル別メトリクス（Gravity.lean 除外）

| ファイル | 行数 | 定理数 | 裸 simp | simp only | simp_all | @[simp] | sorry |
|---|---|---|---|---|---|---|---|
| **CrystalBond.lean** | 963 | 43 | **45** | 50 | 0 | 0 | 0 |
| **GenericBfs.lean** | 501 | 14 | **29** | 25 | 0 | 0 | 0 |
| **Rotate.lean** | 164 | 4 | **39** | 0 | 0 | 21 | 0 |
| **QuarterPos.lean** | 396 | 22 | **18** | 11 | 2 | 2 | 0 |
| **Shatter.lean** | 415 | 21 | **15** | 19 | 1 | 0 | 0 |
| **Shape.lean** | 328 | 15 | **9** | 15 | 0 | 0 | 0 |
| **Cutter.lean** | 275 | 23 | **8** | 7 | 1 | 2 | 0 |
| CrystalGenerator.lean | 57 | 2 | 5 | 0 | 0 | 3 | 0 |
| Painter.lean | 59 | 3 | 6 | 0 | 0 | 3 | 0 |
| Rotate180Lemmas.lean | 111 | 9 | 3 | 5 | 0 | 0 | 0 |
| Stacker.lean | 78 | 1 | 2 | 0 | 0 | 0 | 0 |
| PinPusher.lean | 67 | 1 | 3 | 0 | 0 | 0 | 0 |
| Color.lean | 195 | 6 | 0 | 0 | 0 | 0 | 0 |
| GameConfig.lean | 85 | 4 | 1 | 1 | 0 | 0 | 0 |
| Layer.lean | 83 | 2 | 0 | 2 | 0 | 0 | 0 |
| PartCode.lean | 118 | 3 | 0 | 0 | 0 | 0 | 0 |
| Quarter.lean | 86 | 1 | 0 | 0 | 0 | 0 | 0 |

**合計（Gravity.lean 除外）**: 裸 simp **183 個**、定理 **174 個**

### 1.2 問題の深刻度ランキング

| 優先度 | ファイル | 主な問題 | 影響度 |
|---|---|---|---|
| **S** | GenericBfs.lean | 裸 simp 29個/501行。BFS 基盤全体に影響 | 高 |
| **S** | CrystalBond.lean | 裸 simp 45個、cases 4段ネスト。最大ファイル | 高 |
| **A** | QuarterPos.lean | 裸 simp 18個、66行超の巨大証明 | 高 |
| **A** | Rotate.lean | 裸 simp 39個（全て）。ただし構造的に単純 | 中 |
| **B** | Shatter.lean | 裸 simp 15個、simp_all 混在、decide 18箇所 | 中 |
| **B** | Shape.lean | 裸 simp 9個、41行の ofString_toString | 中 |
| **B** | Cutter.lean | 裸 simp 8個、simp_all 1箇所 | 低 |
| **C** | 小規模ファイル群 | 個別の軽微な改善のみ | 低 |

---

## 2. リファクタリング方針

### 2.1 全体原則

| 原則 | 説明 |
|---|---|
| **simp only 原則** | 全ての裸 `simp` を `simp only [...]` に置換する。`simp?` で最小補題リストを取得 |
| **証明短縮原則** | `omega`, `norm_num`, `decide`, `rfl`, `ext`, `funext` 等のタクティクを積極活用 |
| **補題分割原則** | 30 行超の証明は小補題に分割。各補題は 15 行以内を目標 |
| **@[simp] 設計** | 正規化方向の等式（`rotate180_rotate180`, `isEmpty_rotateCW` 等）に付与 |
| **コメント統一** | 日本語、セクション見出し付き。各ファイル冒頭にモジュール概要 |
| **段階的実行** | ファイル単位で完結させ、各ステップでビルド通過を確認 |

### 2.2 タクティク活用方針

現在使われていない/不足しているタクティクの活用ガイド:

| タクティク | 適用場面 | 現状の問題 |
|---|---|---|
| `simp only [...]` | 全ての simp 呼び出し | 裸 simp が 183 個 |
| `omega` | Nat/Int の線形算術 | GenericBfs で未活用 |
| `decide` | 有限列挙型の全ケース | cases 4段ネストの代替 |
| `fin_cases` | `Direction` 等の有限型分岐 | `cases d1 <;> cases d2` の代替 |
| `ext` / `funext` | 構造体の等価性 | 冗長な field-wise 証明の短縮 |
| `constructor` | 積型の intro | `⟨..., ...⟩` のタクティク版 |
| `simpa` | simp + 仮定で閉じる | `simp [...]; exact h` の短縮 |
| `aesop` | 自動探索 | CrystalBond の複雑分岐で有効な可能性 |
| `tauto` | 命題論理のゴール | GenericBfs の Bool 分岐で有効 |

---

## 3. ファイル別リファクタリング計画

### 3.1 Wave 1: 基盤ファイル（Shape 層）

影響を受けるファイルが多い基盤層から着手する。

#### 3.1.1 Rotate.lean ★★（工数: 小、効果: 中）

**現状**: 裸 simp が 39 個だが、全て `simp [定義名]` の形式で構造的に単純。

**作業内容**:
1. 全 39 個の裸 `simp` を `simp only [...]` に安定化
   - REPL で `simp?` を実行し最小補題リストを取得
   - 例: `simp [rotateCCW, isEmpty_rotateCW]` → `simp only [rotateCCW, isEmpty_rotateCW]`
2. `@[simp]` 属性の見直し: 現在 21 個付与済み。過剰な `@[simp]` がないか確認
   - `rotate180_rotate180` ← 二回適用で恒等 = 正規化方向 ✅
   - `isEmpty_rotateCW` ← isEmpty の保存 ✅
3. `rotateCW` を基本プリミティブとする設計は優秀 → 変更不要

**見積もり**: 定理 4 個 / simp 39 個 → simp? 一括適用で 1-2 時間

---

#### 3.1.2 QuarterPos.lean ★★★（工数: 中、効果: 高）

**現状**: 裸 simp 18 個、巨大定理 `clearPositions_ext` (66 行)、`simp_all` 2 箇所。

**作業内容**:
1. **巨大定理の分割**:
   - `clearPositions_ext` → 3 つの補題に分解:
     - `clearPositions_getQuarter_mem`: positions に含まれる象限がクリアされること
     - `clearPositions_getQuarter_not_mem`: positions に含まれない象限が保存されること
     - `clearPositions_ext`: 上記 2 つから合成
2. **simp 安定化**: 全 18 個を `simp only` に
3. **`simp_all` 除去**: 2 箇所を `simp only` + 明示的仮定適用に分離
4. **`cases d1 <;> cases d2` パターンの整理**:
   - Direction 型の全分岐を `fin_cases` で代替可能か検討
   - `adjacent_rotate180` 等の 16 分岐: `decide` で一発可能か試行
5. **`setQuarter_empty_comm`** の証明簡潔化:
   - `by_cases` + `simp` の連鎖 → `List.set_comm` + `ext` に書き換え

**見積もり**: 定理 22 個 / 証明分割 + simp 安定化

---

#### 3.1.3 Shape.lean ★★★（工数: 中、効果: 高）

**現状**: 裸 simp 9 個、最長 `ofString_toString` が 41 行。decide 8 箇所。

**作業内容**:
1. **`ofString_toString` の分割**:
   - `splitOnColon_intercalate` (ヘルパー) — 既に分離済みか確認
   - `parseLayers_roundtrip`: パース→シリアライズのラウンドトリップ
   - `normalize_roundtrip`: 正規化の冪等性
   - `ofString_toString`: 上記 2 つを合成して 10 行以内に
2. **simp 安定化**: 9 個を `simp only` に
   - 特に `simp [this]` → 仮説名を明示
   - `simp [List.map]` → `simp only [List.map]`
3. **private helper の命名統一**:
   - `quarter_toString_noColon` 等 → ドット記法 (`Quarter.toString_noColon`) に移行検討
4. **`decide` 活用の見直し**:
   - 8 箇所の `decide` が必要な場面か確認
   - `cases` で展開している所で `decide` 一発に置換可能なケースを探す

**見積もり**: 証明分割 + simp 安定化

---

### 3.2 Wave 2: BFS 関連ファイル

BFS 基盤は CrystalBond と Shatter の共通依存。最も負債が大きい領域。

#### 3.2.1 GenericBfs.lean ★★★★（工数: 大、効果: 高）

**現状**: 裸 simp **29 個**、501 行。BFS の健全性・完全性証明が核心。

**作業内容**:
1. **全 29 個の裸 simp を安定化** — 最優先
   - REPL で `simp?` を一括実行
   - `simp_all` → `simp only [...] at *` + 必要な仮定を明示
2. **算術証明の改善**:
   - `add_sq_le_sq_of_lt'` 系の非線形算術 → `omega` / `linarith` の最適解を選定
   - fuel 条件の証明: `Nat.lt_of_lt_of_le` 等の Mathlib 補題に差し替え
3. **Bool 分岐の簡潔化**:
   - `cases h1 : decide (...) <;> cases h2 : decide (...)` パターン
   - → `by_cases` + `tauto` / `omega` で短縮
   - `decide_eq_true_eq` / `decide_eq_false_iff_not` の連鎖を `Bool.decide_eq` 系に統一
4. **match 冗長性の除去**:
   - `cases queue with | nil => ... | cons => ...` → `match` 統一または `List.rec` 活用
5. **証明の分割**:
   - `genericBfs_queue_in_result` (75 行超) → invariant 保存と goal 達成に分離
   - `genericBfs_invariant_preserved` → fuel 管理部と invariant 部を分離

**見積もり**: 最大規模の作業。段階的に simp 安定化 → 算術改善 → 構造改善

---

#### 3.2.2 CrystalBond.lean ★★★★（工数: 大、効果: 高）

**現状**: 裸 simp **45 個**、963 行、プロジェクト最大の非 Gravity ファイル。

**作業内容**:
1. **全 45 個の裸 simp を安定化**
2. **`cases` 4 段ネストの解消**:
   - `isBondedInLayer_symm` の Quarter 型分岐:
     ```lean
     -- 現在: cases q1 <;> cases q2 <;> 各サブケースで rfl/cases
     -- 提案: `decide` で一発解決できるか試行（有限列挙型の Prop）
     ```
   - BFS 関連の case split: `fin_cases` の適用を検討
3. **rotate180 等変性証明のテンプレート化**:
   - `structuralClusterList_rotate180`, `bfs_sound_rotate180` 等が同じパターン
   - 共通パターンを `Rotate180Lemmas.lean` に抽出
   - `map_rotate180_lemma` のような汎用テンプレートを作成
4. **BFS 健全性証明 (`bfs_sound`) の改善**:
   - 現在 70 行超 → 3 つの補題に分割
   - base case / inductive step / queue invariant を分離
5. **`@[simp]` 属性の追加**:
   - `isBondedInLayer_symm` に `@[simp]` 付与（対称性の正規化）
   - `rotate180` 系の基本補題に `@[simp]` 付与

**見積もり**: CrystalBond は GenericBfs と並ぶ最大作業。BFS 証明の構造改善が核心。

---

### 3.3 Wave 3: 加工操作ファイル

#### 3.3.1 Shatter.lean ★★★（工数: 中、効果: 中）

**現状**: 裸 simp 15 個、decide 18 箇所、simp_all 1 箇所。

**作業内容**:
1. **simp 安定化**: 15 個 → `simp only`
2. **decide の最適化**:
   - `shatterTargetsOnCut` の `decide (∃ q ∈ cc, q.dir.isEast = true)`:
     - `List.any` に書き換えて計算効率を改善（定義レベル）
     - ただし定義変更は下流証明に影響 → 互換性を確認
3. **simp_all の除去**:
   - 1 箇所を `simp only [...] at *` に置換
4. **rotate180 等変性の証明パターン統一**:
   - CrystalBond と同様のパターンを共通化
5. **filter 連鎖の整理**:
   - `fragilePositions_map_rotate180` 等: `List.filter_map` の Mathlib 補題活用

**見積もり**: 中程度。decide の定義変更判断が肝要。

---

#### 3.3.2 Cutter.lean ★★（工数: 小、効果: 中）

**現状**: 裸 simp 8 個、概ね良好。simp_all 1 箇所。

**作業内容**:
1. **simp 安定化**: 8 個 → `simp only`
2. **`simp_all` 除去**: 1 箇所
3. **`normalize_rotate180`** の証明簡潔化:
   - `s.normalize_map_layers` への依存を直接化
4. **`cut_rotate180_comm` の依存整理**:
   - 現在 `settleAfterCut_rotate180` + `shatterOnCut_rotate180_comm` に依存
   - 依存グラフを文書化

**見積もり**: 小規模。simp 安定化が主。

---

#### 3.3.3 小規模ファイル群（CrystalGenerator / Painter / PinPusher / Stacker / Rotate180Lemmas）

**作業内容** (一括):
1. **simp 安定化**:
   - CrystalGenerator: 5 個
   - Painter: 6 個
   - PinPusher: 3 個 (→ `List.cons_ne_nil` 等に直接化)
   - Stacker: 2 個
   - Rotate180Lemmas: 3 個
2. **`@[simp]` 属性の見直し**:
   - CrystalGenerator: 3 個付与済み ← 適正
   - Painter: 3 個付与済み ← 適正
3. **PinPusher の `by simp` → 明示化**:
   - `⟨Layer.empty :: s.layers, by simp⟩` → `⟨..., List.cons_ne_nil _ _⟩`

**見積もり**: 各ファイル 30 分程度。一括処理可能。

---

### 3.4 Wave 4: Shape 基底層の仕上げ

#### 3.4.1 Color.lean / PartCode.lean / Quarter.lean / Layer.lean / GameConfig.lean

**現状**: これらは既に高品質。Color.lean は simp 0、decide 活用済み。

**作業内容**:
1. **GameConfig.lean**: 裸 simp 1 個のみ → 安定化
2. **コメント統一**: 各ファイル冒頭にモジュール概要コメントを確認・追加
3. **`@[simp]` 設計レビュー**:
   - Color の `mix_comm`, `mix_self` に `@[simp]` 付与を検討
   - Layer の基本操作に `@[simp]` 付与を検討

**見積もり**: 最小限。品質確認が主。

---

## 4. 横断的改善事項

### 4.1 `@[simp]` 属性の設計基準

以下の基準を全ファイルに統一適用する:

| 付与する | 付与しない |
|---|---|
| 正規化方向の等式（`rotate180_rotate180 = id`）| 条件付き等式（仮定が複雑なもの） |
| 構造保存の等式（`isEmpty_rotateCW`）| 展開方向が明確でないもの |
| 冪等性（`crystallize_idempotent`）| 双方向に使える等式 |
| 吸収律（`mix_white_left`）| ループの危険があるもの |

### 4.2 共通 rotate180 等変性テンプレート

CrystalBond / Shatter / Cutter / Gravity で繰り返される `*_rotate180` 証明パターン:

```lean
-- パターン: map 関数と rotate180 の可換性
-- f (s.rotate180) = (f s).map rotate180
-- 証明骨格: unfold → simp only [mapLayers, List.map_map] → ext → cases
```

これを `Rotate180Lemmas.lean` に汎用補題として追加:

```lean
-- 提案: レイヤ単位の操作が rotate180 と可換であることの汎用テンプレート
theorem mapLayers_rotate180_comm (f : Layer → Layer)
    (h : ∀ l, f l.rotate180 = (f l).rotate180) (s : Shape) :
    (s.mapLayers f).rotate180 = s.rotate180.mapLayers f := by
  simp only [Shape.rotate180, Shape.mapLayers, List.map_map]
  congr 1
  funext l
  exact (h l).symm
```

### 4.3 コメント統一基準

| 項目 | 基準 |
|---|---|
| ファイル冒頭 | SPDX ヘッダ + 1-2 行のモジュール概要（日本語） |
| セクション見出し | `-- ======= セクション名 =======` 形式 |
| 定理コメント | 非自明な定理のみ。自明な `rfl` 証明にはコメント不要 |
| TODO / HACK | `-- TODO:` / `-- HACK:` プレフィックスで統一 |
| 言語 | 日本語（プロジェクト規約通り） |

---

## 5. 設計見直し: レイヤ数制約の撤廃

### 5.1 現状の問題

`Shape.stack` と `Shape.pinPush` には、入力シェイプのレイヤ数が `config.maxLayers` 以内であることを
前提条件として要求する引数が存在する:

```lean
-- Stacker.lean
def stack (bottom top : Shape) (config : GameConfig)
        (_h_bottom : bottom.layerCount ≤ config.maxLayers)
        (_h_top : top.layerCount ≤ config.maxLayers) : Option Shape := do

-- PinPusher.lean
def pinPush (s : Shape) (config : GameConfig)
        (_h_s : s.layerCount ≤ config.maxLayers) : Option Shape := do
```

これは「まだ必要のない段階で早すぎる制約を適用した」事例である。
Machine.lean のラッパーでも `if h : s.layerCount ≤ config.maxLayers then ... else none` の分岐が発生し、
呼び出し側のコードが不必要に複雑化している。

### 5.2 撤廃方針

**前提条件引数を関数シグネチャから削除し、関数内部で必要に応じて truncate する設計に変更する。**

実際のゲーム処理でも、stack / pinPush は内部で truncate を行っており、
入力レイヤ数の制約は関数の**仕様**ではなく**呼び出し側の最適化**に過ぎない。

#### 変更対象ファイル

| ファイル | 変更内容 |
|---|---|
| `S2IL/Behavior/Stacker.lean` | `_h_bottom`, `_h_top` を削除。関数内の truncate ロジックは維持 |
| `S2IL/Behavior/PinPusher.lean` | `_h_s` を削除。関数内の truncate ロジックは維持 |
| `S2IL/Machine/Machine.lean` | `if h : ... then ... else none` 分岐を除去し、単純な `Option.map` / `Option.bind` に |
| `S2IL/Shape/GameConfig.lean` | `truncate_of_le` 等のレイヤ数前提付き補題の見直し |

#### 変更前後の比較

```lean
-- 変更前: Machine.lean
def pinPush (shape : Option Shape) (config : GameConfig) : Option Shape :=
    match shape with
    | some s =>
        if h : s.layerCount ≤ config.maxLayers then
          s.pinPush config h
        else none
    | none => none

-- 変更後: Machine.lean
def pinPush (shape : Option Shape) (config : GameConfig) : Option Shape :=
    shape.bind (·.pinPush config)
```

```lean
-- 変更前: Machine.lean
def stack (bottom top : Option Shape) (config : GameConfig) : Option Shape :=
    match bottom, top with
    | some b, some t =>
        if h1 : b.layerCount ≤ config.maxLayers then
          if h2 : t.layerCount ≤ config.maxLayers then
            b.stack t config h1 h2
          else none
        else none
    | _, _ => none

-- 変更後: Machine.lean
def stack (bottom top : Option Shape) (config : GameConfig) : Option Shape :=
    match bottom, top with
    | some b, some t => b.stack t config
    | _, _ => none
```

### 5.3 影響範囲

| 影響先 | 影響度 | 対処 |
|---|---|---|
| Gravity.lean の `process_rotate180` | **なし** | process は stack/pinPush を使用しない |
| gravity-proof-cheatsheet.md | **軽微** | Section 0 の「影響なし」注記を撤廃に合わせて更新 |
| `stack_rotate180_comm` (将来) | **簡素化** | レイヤ数制約の propagation が不要に |
| `pinPush_rotate180_comm` (将来) | **簡素化** | 同上 |
| テストコード | **軽微** | レイヤ数証明引数の削除のみ |

### 5.4 チェックリスト

- [ ] `Shape.stack` から `_h_bottom`, `_h_top` 引数を削除
- [ ] `Shape.pinPush` から `_h_s` 引数を削除
- [ ] `Machine.stack` の `if h1 : ... then if h2 : ...` 分岐を除去
- [ ] `Machine.pinPush` の `if h : ...` 分岐を除去
- [ ] `GameConfig.lean` のレイヤ数前提付き補題の見直し
- [ ] `Stacker.lean` のドキュメントコメントから前提条件の記述を削除
- [ ] `PinPusher.lean` のドキュメントコメントから前提条件の記述を削除
- [ ] `gravity-proof-cheatsheet.md` Section 0 の更新
- [ ] `lake build` 通過

---

## 6. 設計見直し: 安定状態 (Settled State) の適切な反映

### 6.1 ゲーム規定の確認

[glossary.md](../shapez2/glossary.md) より:

> ゲーム上、**ベルト** で搬送されるシェイプおよび各 **加工装置** の入出力は常に安定状態であることが保証されている。
> 不安定状態は加工装置の内部処理（切断後の落下、積層後の落下、ピン押し後の落下など）において
> のみ一時的に発生し、落下処理 (Gravity) によって安定状態に復帰した後に出力される。

すなわち:
- **加工装置の入力**: 常に安定状態
- **加工装置の出力**: 常に安定状態（内部で gravity を適用済み）
- **中間処理**: 不安定状態が一時的に発生しうる

### 6.2 現状の問題

**`Shape.IsSettled`** は `Gravity.lean` で定義されているが、以下の問題がある:

1. **Machine.lean で未使用**: Machine ラッパーの入力に `IsSettled` 前提がない
2. **Behavior 関数で未使用**: 安定状態でのみ意味を持つ操作（着色・結晶化・回転）の関数にも
   `IsSettled` 前提がない
3. **証明への影響**: 安定状態の前提があれば簡素化できる証明が、不必要に一般的な形で書かれている可能性

### 6.3 Behavior 操作の安定状態分類

| 操作 | 関数 | 安定状態前提 | 理由 |
|---|---|---|---|
| 着色 (Paint) | `Shape.paint` | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| 結晶化 (Crystallize) | `Shape.crystallize` | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| 回転 (Rotate) | `Shape.rotateCW` 等 | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| 切断 (Cut) | `Shape.cut` | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| スワップ (Swap) | `Shape.swap` | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| ピン押し (PinPush) | `Shape.pinPush` | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| 積み重ね (Stack) | `Shape.stack` | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| 切断処理 (HalfDestroy) | `Shape.halfDestroy` | **追加すべき** | 加工装置からのみトリガ。入力は常に安定 |
| 落下 (Gravity) | `Gravity.process` | **不要** | 中間処理。不安定状態の入力を安定化する |
| 砕け散り (Shatter) | `Shatter.*` | **不要** | 中間処理。stack/cut の内部工程で発生 |
| 半分抽出 (EastHalf 等) | `Layer.eastHalf` 等 | **不要** | 基本プリミティブ。cut 内部で使用 |

### 6.4 実装方針

#### 段階 A: Machine.lean へのIsSettled 前提の追加

Machine レベルのラッパー関数に `IsSettled` 前提を追加する。
これによりゲーム規定がコード上で明示される:

```lean
-- 変更後: Machine.lean
def paint (shape : Option Shape) (color : Option Color)
    (h_settled : ∀ s, shape = some s → s.IsSettled) : Option Shape :=
    match shape, color with
    | some s, some c => some (s.paint c)
    | _, _ => none
```

ただし、`Option` ラッパーに `IsSettled` 前提を持たせる設計は冗長になりうる。
代替として、**入力の `Shape` 型自体に安定状態を内包するサブタイプ**を検討:

```lean
-- 代替案: SettledShape サブタイプ
structure SettledShape where
    shape : Shape
    settled : shape.IsSettled

-- Machine は SettledShape を入出力とする
def Machine.paint (shape : Option SettledShape) (color : Option Color) : Option SettledShape := ...
```

**推奨: 段階的に導入**。まずは Behavior 関数に `IsSettled` 前提を追加し、
`SettledShape` サブタイプの導入は将来の検討事項とする。

#### 段階 B: Behavior 関数への前提追加

安定状態でのみ呼ばれる Behavior 関数に `(h : s.IsSettled)` 前提を追加。
ただし、この前提は**定理で活用される仮定**であり、関数の計算結果を変えない:

```lean
-- 着色: 安定状態仮定を追加（計算結果には影響なし、定理で活用）
-- ※ 安定状態仮定は定理側でのみ使用し、定義本体は変更しない
theorem paint_preserves_settled (s : Shape) (c : Color) (h : s.IsSettled) :
    (s.paint c).IsSettled := by ...
```

**重要**: 定義（`def`）自体に前提を追加するのではなく、**定理（`theorem`）に前提を追加する**
アプローチを推奨。定義の変更は下流への影響が大きいが、定理の追加は安全。

### 6.5 安定状態保存定理のロードマップ

以下の定理を段階的に証明する:

| 定理 | 内容 | 前提 | 難度 |
|---|---|---|---|
| `paint_preserves_settled` | 着色は安定状態を保存 | `IsSettled` | ★ |
| `crystallize_preserves_settled` | 結晶化は安定状態を保存 | `IsSettled` | ★ |
| `rotateCW_preserves_settled` | 回転は安定状態を保存 | `IsSettled` | ★★ |
| `rotate180_preserves_settled` | 180° 回転は安定状態を保存 | `IsSettled` | ★ (既存) |
| `gravity_produces_settled` | 落下結果は安定状態 | なし | ★★★ |
| `cut_produces_settled` | 切断結果は安定状態 | `IsSettled` | ★★★ |
| `stack_produces_settled` | 積層結果は安定状態 | `IsSettled` × 2 | ★★★★ |

`gravity_produces_settled` は全ての `*_produces_settled` 定理の基盤となる。
切断・積層は内部で gravity を呼ぶため、gravity の安定状態出力が鍵。

### 6.6 チェックリスト

- [ ] `IsSettled` の定義を Gravity.lean から独立ファイルへ移動（循環依存回避）を検討
- [ ] `paint_preserves_settled` の証明
- [ ] `crystallize_preserves_settled` の証明
- [ ] `rotateCW_preserves_settled` の証明
- [ ] Machine.lean に安定状態の方針コメントを追加
- [ ] `gravity_produces_settled` の証明（中期目標）

---

## 7. ドメインドキュメント (`docs/shapez2`) の改善計画

### 7.1 現状評価

| ファイル | 行数 | 品質 | 主な問題 |
|---|---|---|---|
| `glossary.md` | ~400 | ★★★★★ | 安定状態の記載が完璧。改善不要 |
| `adjacency.md` | ~240 | ★★★★★ | 厳密で視覚的。改善不要 |
| `crystal-shatter.md` | ~300 | ★★★★ | 良好。コード実装との対応更新のみ |
| `mam.md` | ~300 | ★★★★ | 良好。Insane モードへの言及追加が望ましい |
| `falling.md` | ~400 | ★★★ | **安定状態の記載が完全に欠落** |
| `README.md` | ~100 | ★★★★ | 良好。安定状態ドキュメントへのリンク追加のみ |

### 7.2 falling.md の改善（最優先）

**問題**: `falling.md` は落下処理のアルゴリズムを詳細に記述しているが、
落下処理の**目的**である「不安定状態 → 安定状態への変換」という観点が完全に欠落。

**追加すべき内容**:

1. **セクション追加: 安定状態と落下処理の関係**
   ```markdown
   ## 安定状態 (Settled State) と落下処理
   
   落下処理の目的は、不安定状態のシェイプを安定状態に変換することである。
   
   - **安定状態の定義**: 浮遊する落下単位が存在しない状態
   - **ゲーム規定**: 加工装置の入出力は常に安定状態
   - **落下処理の保証**: process(s) の結果は常に安定状態（または empty）
   
   ### 安定状態の Lean 定義
   
   `Shape.IsSettled` は `floatingUnits` が空であることで定義される。
   ```

2. **セクション追加: 落下処理が発生する文脈**
   - 切断後: 切断で分離された半分に浮遊部分が生じる場合
   - 積層後: 上側シェイプの一部が下側の空象限を通過して落下する場合
   - ピン押し後: レイヤ上限超過による truncate で浮遊部分が生じる場合

3. **既存セクションへの cross-reference 追加**:
   - `glossary.md` の安定状態定義への参照
   - Lean コード `Shape.IsSettled`, `Shape.isSettled` への参照

### 7.3 crystal-shatter.md の軽微な改善

- 実装が完了している旨の反映（`shatterOnCut`, `shatterOnFall` が実装済み）
- `Shatter.lean` のコード参照を更新

### 7.4 mam.md の軽微な改善

- Insane モード（5 層、`GameConfig.vanilla5`）への言及追加
- `GameConfig` の Lean 定義への参照

### 7.5 glossary.md の安定状態セクション拡充検討

現在の glossary.md の安定状態記述は十分に良好だが、以下を検討:

- `IsSettled` の Lean 定義への参照追加
- 安定状態が保存される操作の一覧表（着色・回転等で安定状態が壊れないこと）

### 7.6 チェックリスト

- [ ] `falling.md`: 安定状態セクションの追加
- [ ] `falling.md`: 落下処理が発生する文脈のセクション追加
- [ ] `falling.md`: cross-reference の追加（glossary.md, Lean コード）
- [ ] `crystal-shatter.md`: 実装完了の反映
- [ ] `mam.md`: Insane モードへの言及
- [ ] `glossary.md`: IsSettled の Lean 定義への参照追加（オプション）
- [ ] `README.md`: 安定状態に関する参照パスの追加

---

## 8. 実行スケジュール

### 実行順序と依存関係

```
Wave 0 (設計見直し) ← Wave 1-4 の前提
├── レイヤ数制約の撤廃 (Section 5)
├── 安定状態の方針決定 (Section 6)
└── docs/shapez2 の改善 (Section 7)

Wave 1 (基盤 Shape 層) ← 他の全てが依存
├── Rotate.lean          ← CrystalBond, Shatter, Cutter が依存
├── QuarterPos.lean      ← CrystalBond, Shatter, Gravity が依存
└── Shape.lean           ← 全ファイルが依存

Wave 2 (BFS 関連) ← Shatter が依存
├── GenericBfs.lean      ← CrystalBond が依存
└── CrystalBond.lean     ← Shatter, Gravity が依存

Wave 3 (加工操作)
├── Shatter.lean         ← Cutter, Stacker, Gravity が依存
├── Cutter.lean          ← 独立
└── 小規模ファイル群     ← 独立

Wave 4 (Shape 基底層) ← 独立
└── Color / PartCode / Quarter / Layer / GameConfig
```

### 各 Wave の完了条件

| Wave | 完了条件 |
|---|---|
| Wave 0 | レイヤ数制約撤廃完了、安定状態方針決定、docs 改善完了、`lake build` 通過 |
| Wave 1 | 対象ファイルの裸 simp = 0、巨大証明なし、`lake build` 通過 |
| Wave 2 | 対象ファイルの裸 simp = 0、cases 3段以下、`lake build` 通過 |
| Wave 3 | 対象ファイルの裸 simp = 0、`lake build` 通過 |
| Wave 4 | コメント統一、`@[simp]` 設計適用、`lake build` 通過 |

---

## 9. リスク・注意事項

| リスク | 対策 |
|---|---|
| simp only 化で証明が壊れる | REPL で `simp?` → 最小補題リストを取得してから置換 |
| 補題分割で名前空間が汚染される | `private` を積極活用。公開 API を最小に |
| Gravity.lean への影響 | Gravity.lean が依存する基盤補題の**型シグネチャ**は変更しない。証明本体のみ変更 |
| 大規模変更でのリグレッション | Wave ごとにビルド通過を確認。1 ファイル完了ごとに中間コミット |
| @[simp] 追加で既存証明が壊れる | 追加前に `lake build` でリグレッションチェック |
| レイヤ制約撤廃で既存テストが壊れる | 引数削除のみ。関数のロジックは不変。テストの引数削除で対応 |
| IsSettled 前提追加で下流が壊れる | **定理（theorem）への追加のみ**。定義（def）は変更しない方針 |

### Gravity.lean との境界

以下の補題は Gravity.lean が依存しているため、**型シグネチャの変更は禁止**:

- `QuarterPos.rotate180_rotate180`
- `QuarterPos.clearPositions_ext`
- `QuarterPos.setQuarter_empty_comm`
- `Shape.rotate180`, `Shape.mapLayers`
- `Layer.rotate180`, `Layer.isEmpty_rotate180`
- `CrystalBond.*` (structuralClusterList 関連)
- `Shatter.shatterOnCut_rotate180_comm`, `shatterOnFall_rotate180_comm`
- `GenericBfs.*` (BFS 健全性定理)

これらの**証明本体**はリファクタリング可能だが、名前・引数順・戻り値型は維持する。

---

## 10. 成功指標

| 指標 | 現状 | 目標 |
|---|---|---|
| 裸 simp 数（Gravity 除外） | 183 個 | **0 個** |
| simp_all 数 | 4 個 | **0 個**（`simp only [...] at *` に置換） |
| 30 行超の証明数 | 5+ 個 | **0 個** |
| `@[simp]` 設計基準の明文化 | なし | **完了** |
| ファイル冒頭コメント | 不統一 | **全ファイル統一** |
| レイヤ数制約引数 | 3 個 | **0 個** |
| 安定状態保存定理 | 1 個 (rotate180) | **3+ 個** (paint, crystallize, rotate) |
| `falling.md` の安定状態記載 | なし | **完了** |
| `lake build` 通過 | ✅ | ✅（常に維持） |

---

## 11. 各 Wave の詳細チェックリスト

### Wave 0 チェックリスト（設計見直し）

- [ ] `Shape.stack` から `_h_bottom`, `_h_top` 引数を削除（Section 5）
- [ ] `Shape.pinPush` から `_h_s` 引数を削除（Section 5）
- [ ] `Machine.lean` の layerCount 分岐を除去（Section 5）
- [ ] `falling.md` に安定状態セクションを追加（Section 7）
- [ ] `crystal-shatter.md` の実装状況を反映（Section 7）
- [ ] 安定状態の方針をコメントで明記（Section 6）
- [ ] Wave 0 完了: `lake build` 通過

### Wave 1 チェックリスト

- [ ] Rotate.lean: 裸 simp 39 個 → simp only 化
- [ ] Rotate.lean: @[simp] 属性レビュー（21 個）
- [ ] QuarterPos.lean: clearPositions_ext の補題分割
- [ ] QuarterPos.lean: 裸 simp 18 個 → simp only 化
- [ ] QuarterPos.lean: simp_all 2 個 → 除去
- [ ] QuarterPos.lean: Direction 分岐の fin_cases / decide 検討
- [ ] Shape.lean: ofString_toString の補題分割
- [ ] Shape.lean: 裸 simp 9 個 → simp only 化
- [ ] Wave 1 完了: `lake build` 通過

### Wave 2 チェックリスト

- [ ] GenericBfs.lean: 裸 simp 29 個 → simp only 化
- [ ] GenericBfs.lean: Bool 分岐の簡潔化（tauto / omega）
- [ ] GenericBfs.lean: 75 行超の証明分割
- [ ] CrystalBond.lean: 裸 simp 45 個 → simp only 化
- [ ] CrystalBond.lean: cases 4段ネスト → decide / fin_cases
- [ ] CrystalBond.lean: bfs_sound の 70 行超 → 分割
- [ ] CrystalBond.lean: rotate180 等変性テンプレート抽出
- [ ] Wave 2 完了: `lake build` 通過

### Wave 3 チェックリスト

- [ ] Shatter.lean: 裸 simp 15 個 → simp only 化
- [ ] Shatter.lean: simp_all 1 個 → 除去
- [ ] Shatter.lean: decide 定義の最適化検討
- [ ] Cutter.lean: 裸 simp 8 個 → simp only 化
- [ ] Cutter.lean: simp_all 1 個 → 除去
- [ ] CrystalGenerator.lean: 裸 simp 5 個 → simp only 化
- [ ] Painter.lean: 裸 simp 6 個 → simp only 化
- [ ] PinPusher.lean: `by simp` 3 個 → 明示的証明
- [ ] Stacker.lean: 裸 simp 2 個 → simp only 化
- [ ] Rotate180Lemmas.lean: 裸 simp 3 個 → simp only 化
- [ ] 共通テンプレート: mapLayers_rotate180_comm の追加
- [ ] Wave 3 完了: `lake build` 通過

### Wave 4 チェックリスト

- [ ] GameConfig.lean: 裸 simp 1 個 → simp only 化
- [ ] 全ファイル: ファイル冒頭コメント統一
- [ ] 全ファイル: @[simp] 設計基準の適用レビュー
- [ ] Wave 4 完了: `lake build` 通過

---

## 12. simp only 化の作業手順（共通）

各ファイルの simp only 化は以下の統一手順で実施する:

1. **対象行の特定**: `grep -n '\bsimp\b' <file>` で裸 simp 行を列挙
2. **REPL で simp? 実行**: 各 simp 行をタクティクモードで `simp?` に置換して実行
3. **最小補題リストの取得**: REPL 出力から `Try this: simp only [...]` を抽出
4. **置換**: 元の `simp [...]` を `simp only [...]` に書き換え
5. **ビルド確認**: `lake build` で全体のリグレッションチェック

`lean-simp-stabilizer` エージェントで自動化可能。

---

## 13. 参考情報

| 参照 | 用途 |
|---|---|
| `.github/skills/lean-simp-guide/SKILL.md` | simp 系タクティクの使い分け・安定化移行ガイド |
| `.github/skills/lean-tactic-select/SKILL.md` | ゴール形状 → タクティク選定 |
| `.github/skills/lean-repl/SKILL.md` | REPL での simp? 実行手順 |
| `docs/lean/tactics/index.md` | タクティク一覧 |
| `docs/knowledge/lean-proof-tips.md` | 証明パターン集 |
| `docs/shapez2/glossary.md` | 安定状態 (Settled State) の公式定義 |
| `docs/shapez2/falling.md` | 落下処理の仕様（安定状態セクション追加予定） |
| `docs/shapez2/crystal-shatter.md` | 砕け散りの仕様 |
