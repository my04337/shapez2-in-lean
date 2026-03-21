# コードレビュー & 改善計画

フェーズ 1 (Shape Code Notation + Shape Processing 装置) の実装完了時点でのコードレビュー結果と、
今後の改善計画をまとめる。

---

## 1. レビュー方針の妥当性評価

ユーザが提示した3つの方針について評価する。

### 1-1. 「Lean としてより自然な表現で記述できているか」

**評価: 方針は妥当。実際に修正すべき箇所がある。**

主に**コードの重複**が問題であり、Lean の言語機能を活かした統合が必要。
一方、各型の定義・加工操作の基本設計は適切で、Layer → Shape の二段構成パターンが
一貫して使われている点は良い。

### 1-2. 「不足している証明がどれぐらいあるか」

**評価: 方針は妥当。証明の不足は大きい。**

回転操作は豊富な証明があるが、他の加工操作（着色・結晶製造・積層・切断・落下・ピン押し）は
定理が皆無または `sorry` のみ。メインとなるシェイプ定義・加工ロジックの証明を段階的に
追加する計画が必要。

### 1-3. 「toString/ofString の証明を優先しない」

**評価: 方針は妥当。**

現時点で `sorry` になっている4箇所（Shape.lean の文字列ラウンドトリップ関連）は
いずれもシリアライズ固有の補助定理であり、加工ロジックの正しさには無関係。
`List Char` レベルの煩雑な証明が必要になるため、優先度を下げるのは合理的。

---

## 2. 現状のコード品質課題

### 2-1. コード重複

| # | 重複箇所 | ファイル | 内容 |
|---|---|---|---|
| D-1 | `shatterOnTruncate` | `Stacker.lean` / `PinPusher.lean` | **完全に同一の実装**が2つの名前空間に存在。共通関数に統合すべき |
| D-2 | `removePositions` / `clearPositions` | `Gravity.lean` / `Shatter.lean` | **完全に同一の実装**。`Gravity.removePositions` (private) は `Shape.clearPositions` の重複。`Gravity` 側を削除し `Shape.clearPositions` を利用すべき |
| D-3 | `emptyLayer` | `PinPusher.lean` / `Cutter.lean` | **完全に同一の定義**。`Layer` 名前空間に `Layer.empty` として統合すべき |
| D-4 | BFS パターン | `CrystalBond.lean` / `Gravity.lean` (×2) | 同構造のBFS実装が3箇所。エッジ述語のみ異なる。汎用BFSの抽出を検討 |
| D-5 | クラスタ収集パターン | `CrystalBond.lean` / `Gravity.lean` | `foldl` で重複除去しながらクラスタを収集するパターンが重複 |

**優先度**: D-1 〜 D-3 は即時修正すべき。D-4, D-5 は設計判断を要するため後回し可。

### 2-2. `sorry` の一覧（未完了の証明）

| # | ファイル | 定理名 | 分類 |
|---|---|---|---|
| S-1 | `Shape.lean` | `splitOnColon_intercalate` | 文字列ラウンドトリップ (低優先) |
| S-2 | `Shape.lean` | `dropTrailingEmpty_spec` | 文字列ラウンドトリップ (低優先) |
| S-3 | `Shape.lean` | `normalize_of_isNormalized` | 正規化 (中優先) |
| S-4 | `Shape.lean` | `ofString_toString` | 文字列ラウンドトリップ (低優先) |
| S-5 | `Cutter.lean` | `eastHalf_westHalf_combine` | 加工ロジック (**高優先**) |
| S-6 | `Cutter.lean` | `cut_rotate180_comm` | 加工ロジック (**高優先**) |
| S-7 | `Cutter.lean` | `swap_self` | 加工ロジック (中優先) |
| S-8 | `Shatter.lean` | `shatterOnCut_rotate180_comm` | 加工ロジック (**高優先**) |
| S-9 | `Shatter.lean` | `shatterOnFall_rotate180_comm` | 加工ロジック (**高優先**) |

### 2-3. 定理が未定義の加工操作

以下の加工操作には定理が **1つも存在しない**。
主要な性質を定義・証明することで、実装の正しさが保証される。

| # | モジュール | 証明すべき主要性質 |
|---|---|---|
| P-1 | **CrystalGenerator** | 冪等性、着色象限の保存、空/ピンの結晶充填 |
| P-2 | **Painter** | 冪等性、非着色象限の保存、最上位レイヤのみ変更 |
| P-3 | **CrystalBond** | 結合関係の対称性、クラスタの健全性 |
| P-4 | **Gravity** | 構造結合の対称性、落下の冪等性 |
| P-5 | **PinPusher** | レイヤ数増加、ピン生成の正確性 |
| P-6 | **Stacker** | 配置の正確性 (レイヤ構成) |

### 2-4. 矛盾の可能性が低い点

精査の結果、同種の処理間で **矛盾する実装は見つからなかった**。
重複しているコードは全て同一のロジックを持っており、
一方を変更して他方を更新し忘れるリスクがあるため統合が望ましい。

---

## 3. 証明方針

### 3-1. 基本原則

- **証明は内部表現 (構造体/帰納型) に対して行う**。
  `toString` / `ofString` で文字列に変換してから比較する方式は使わない。
- **`sorry` は段階的に解消する**。一度に全て証明するのではなく、
  優先度に従って計画的に進める。
- **テスト (`#eval`) は証明の代替にはならない** が、
  仕様理解と実装の妥当性確認には有用であり、引き続き維持する。

### 3-2. 優先度

| 優先度 | 対象 | 理由 |
|---|---|---|
| **高** | 加工操作の代数的性質 (冪等性、可換性、逆元) | 操作の正しさの核心。フェーズ 2 の加工フロー表現に直結 |
| **高** | 既存 `sorry` の解消 (S-5 〜 S-9) | 既に定理文が存在し、設計意図が明確 |
| **中** | 各操作のプリミティブ性質 (象限/レイヤレベルの保存則) | 高優先の証明の基礎となる補題 |
| **中** | 正規化に関する証明 (S-3) | 多くの操作の後処理で使われる |
| **低** | 文字列ラウンドトリップ (S-1, S-2, S-4) | 加工ロジックの正しさに無関係 |

### 3-3. 証明パターンの指針

| パターン | 適用場面 | 例 |
|---|---|---|
| `cases ... <;> rfl` | 有限型の全パターン網羅 | `Quarter`, `Color`, `Direction` |
| `ext <;> simp [...]` | 構造体の等価性 + simp 補題 | `Shape.rotateCW_four` |
| `induction ... with` | リスト帰納法 | `List Layer` に対する証明 |
| `omega` | 自然数の不等式 | `layerCount`, `truncate` 関連 |

---

## 4. 改善計画

### Phase A: 重複コードの統合 (即時)

**目標**: 重複を排除し、1つの変更が他に波及するリスクを解消する。

| # | タスク | 対象ファイル |
|---|---|---|
| A-1 | `Layer.empty` を `Layer` 名前空間に定義し、`PinPusher.emptyLayer` と `Cutter.emptyLayer` を置換 | `Layer.lean`, `PinPusher.lean`, `Cutter.lean` |
| A-2 | `Gravity.removePositions` を削除し、`Shape.clearPositions` を利用 | `Gravity.lean` |
| A-3 | `shatterOnTruncate` を `Shape` 名前空間に統合し、`Stacker` / `PinPusher` 双方から参照 | `Shatter.lean` (or 新設), `Stacker.lean`, `PinPusher.lean` |

### Phase B: 基本性質の証明 (短期)

各加工操作のレイヤ/象限レベルの基本性質を証明する。
高優先の `sorry` 解消のための基礎補題にもなる。

| # | タスク | 対象ファイル |
|---|---|---|
| B-1 | `CrystalGenerator.fillQuarter` の保存則: `colored` 象限は不変 | `CrystalGenerator.lean` |
| B-2 | `CrystalGenerator.fillLayer` / `crystallize` の冪等性 | `CrystalGenerator.lean` |
| B-3 | `Painter.paintQuarter` の保存則: 非 `colored` 象限は不変 | `Painter.lean` |
| B-4 | `Painter.paintLayer` / `paint` の冪等性 | `Painter.lean` |
| B-5 | `CrystalBond.isBonded` の対称性 | `CrystalBond.lean` |
| B-6 | `Gravity.isStructurallyBonded` の対称性 | `Gravity.lean` |
| B-7 | `PinPusher.liftUp` のレイヤ数性質 | `PinPusher.lean` |
| B-8 | `Stacker.placeAbove` のレイヤ数性質 | `Stacker.lean` |

### Phase C: 既存 `sorry` の解消 (中期)

| # | タスク | 対象ファイル | 依存 |
|---|---|---|---|
| C-1 | `Shape.eastHalf_westHalf_combine` | `Cutter.lean` | — |
| C-2 | `Shape.cut_rotate180_comm` | `Cutter.lean` | Phase B, Shatter sorry |
| C-3 | `Shape.shatterOnCut_rotate180_comm` | `Shatter.lean` | CrystalBond の 180° 回転補題 |
| C-4 | `Shape.shatterOnFall_rotate180_comm` | `Shatter.lean` | 同上 |
| C-5 | `Shape.normalize_of_isNormalized` | `Shape.lean` | — |
| C-6 | `Shape.swap_self` | `Cutter.lean` | C-1, C-3 |

### Phase D: 文字列ラウンドトリップ (低優先・任意)

| # | タスク | 対象ファイル |
|---|---|---|
| D-1 | `splitOnColon_intercalate` | `Shape.lean` |
| D-2 | `dropTrailingEmpty_spec` | `Shape.lean` |
| D-3 | `ofString_toString` | `Shape.lean` |

---

## 5. ドキュメント整備

本計画自体がドキュメントとして機能するが、追加で以下を整備する。

| # | タスク | 対象 |
|---|---|---|
| E-1 | `MILESTONES.md` のタスク 1-2-4 (切断系操作の基本性質の証明) を Phase B, C で具体化 | `docs/MILESTONES.md` |
| E-2 | `lean-proof-tips.md` に新しい証明パターン (ext, omega, BFS 関連) を追記 | `docs/knowledge/lean-proof-tips.md` |
| E-3 | 本ドキュメントの方針セクション (§3) を `copilot-instructions.md` の証明方針として反映 | `.github/copilot-instructions.md` |

---

## 6. 作業優先順序

```
Phase A (重複統合)
  ↓
Phase B (基本性質の証明)
  ↓
Phase C (既存 sorry の解消)
  ↓
Phase D (文字列ラウンドトリップ, 任意)
  ↓
Phase E (ドキュメント整備, 各 Phase と並行可)
```

Phase A は即時実行可能で他のPhaseの前提となる。
Phase B は Phase C の補題として必要になるため先に着手する。
Phase E はドキュメント更新のため、各Phase完了時に随時実施する。
