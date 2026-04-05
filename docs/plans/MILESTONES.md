# マイルストーン チェックシート

Shapez2 in Lean (S2IL) の開発マイルストーンと達成状況を管理するチェックシートです。

---

## フェーズ 0: 事前準備

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| 0-1 | ツールチェインの構築 (elan / lake / lean) | ✅ 完了 | |
| 0-2 | 用語集の作成・拡充 (`docs/GLOSSARY.md`) | ✅ 完了 | |

---

## フェーズ 1: Lean での基礎的な定義

シェイプおよび加工装置・信号装置の型・関数を Lean で形式的に定義する。

### 1-1. Shape Code Notation の形式化

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| 1-1-1 | **Part Code** の列挙型定義 (`Circle`, `Rectangle`, `Star`, `Windmill`, `Pin`, `Crystal`) | ✅ 完了 | |
| 1-1-2 | **Color** の列挙型定義 (`Red`, `Green`, `Blue`, `Yellow`, `Cyan`, `Magenta`, `White`, `Uncolored`) | ✅ 完了 | |
| 1-1-3 | **Quarter** (象限) の型定義 (Part Code × Color の組、および空の象限) | ✅ 完了 | |
| 1-1-4 | **Layer** (レイヤ) の型定義 (4 象限の組) | ✅ 完了 | |
| 1-1-5 | **Shape** (シェイプ) の型定義 (1〜4 レイヤの積み重ね) | ✅ 完了 | 構造体 `{ layers : List Layer, layers_ne }` にリファクタリング済み |
| 1-1-6 | Shape Code 文字列とのパース・シリアライズ関数の実装 | ✅ 完了 | |
| 1-1-7 | Shape Code のパース・シリアライズの正当性検証 (ラウンドトリップ定理) | ✅ 完了 | |

### 1-2. Shape Processing 装置の定義

加工操作を純粋関数として定義する。

#### 切断 (Cutting)

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| 1-2-1 | **Half-Destroyer** (切断処理機): West Half を削除する関数 | ✅ 完了 | |
| 1-2-2 | **Cutter** (切断機): West Half と East Half に分割する関数 | ✅ 完了 | |
| 1-2-3 | **Swapper** (スワップ機): 2 つのシェイプの West Half を入れ替える関数 | ✅ 完了 | |
| 1-2-4 | 切断系操作の基本性質の証明 | 🔄 進行中 | `eastHalf_westHalf_combine` ✅, `swap_self` ✅, `combineHalves_self` ✅, `cut_rotate180_comm` sorry（`process_rotate180` の sorry 1件に依存。証明チェーン再構築中。詳細: [gravity-proof-execution-plan.md](gravity-proof-execution-plan.md) Wave 3〜5） |

#### 回転 (Rotating)

| # | タスク | 状態 |
|---|---|---|
| 1-2-5 | **Rotator** (回転機): 時計回り 90° 回転関数 | ✅ 完了 |
| 1-2-6 | **Reverse Rotator** (逆回転機): 反時計回り 90° 回転関数 | ✅ 完了 |
| 1-2-7 | **180° Rotator** (180 度回転機): 180° 回転関数 | ✅ 完了 |
| 1-2-8 | 回転の合成・逆元に関する定理 (例: 4 回回転 = 恒等) | ✅ 完了 |

#### 積み重ね (Stacking)

| # | タスク | 状態 |
|---|---|---|
| 1-2-9 | **Stacker** (積層機): 2 つのシェイプを積み重ねる関数 (レイヤ上限の切り捨てを含む) | ✅ 完了 | レイヤ数上限制約 (`h_bottom`, `h_top`) 追加済み。工程5a (`shatterOnTruncate`) 削除済み |
| 1-2-10 | 積み重ね時の落下ルールの形式化 (空象限・欠落パーツの落下挙動) | ✅ 完了 |

#### 着色 (Painting)

| # | タスク | 状態 |
|---|---|---|
| 1-2-11 | **混色** (Color Mixing) 関数の定義 (Mixing Rules に基づく) | ✅ 完了 |
| 1-2-12 | **Painter** (着色機): 最上位レイヤを着色する関数 | ✅ 完了 |
| 1-2-13 | 混色の可換性・冪等性・恒等元・非結合性の証明 | ✅ 完了 |

#### ピン押し・結晶 (Pin Pushing / Crystals)

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| 1-2-14 | **Pin Pusher** (ピン押し機): 第 1 レイヤの非空象限の下にピンを追加する関数 | ✅ 完了 | レイヤ数上限制約 (`h_s`) 追加済み |
| 1-2-15 | **Crystal Generator** (結晶製造機): 液剤でギャップ・ピンを結晶に充填する関数 | ✅ 完了 | |
| 1-2-16 | 結晶の **Fragile** 性 (落下・切断による Shatter) の形式化 | ✅ 完了 | `isFragile`, `QuarterPos`, `CrystalBond`, `Shatter` 全実装済み。回転等変性の証明完了（BFS 完全性をポテンシャル関数で証明、sorry 0件） |

### 1-3. Wires and Logic 装置の定義

| # | タスク | 状態 |
|---|---|---|
| 1-3-1 | **Logical Signal** の型定義 (`Number`, `Color`, `ShapeCode`, `Empty`, `Conflict`) | ⬜ 未着手 |
| 1-3-2 | On / Off 分類関数の定義 | ⬜ 未着手 |
| 1-3-3 | **AND Gate / OR Gate / NOT Gate / XOR Gate** の関数定義 | ⬜ 未着手 |
| 1-3-4 | **Comparison Gate** (比較ゲート) の 6 条件の定義 | ⬜ 未着手 |
| 1-3-5 | **Belt Filter** (ベルトフィルター) の動作関数の定義 | ⬜ 未着手 |
| 1-3-6 | **Pipe Gate** (パイプゲート) の動作関数の定義 | ⬜ 未着手 |
| 1-3-7 | **Signal Producer** (信号生成器) の定義 | ⬜ 未着手 |
| 1-3-8 | 論理ゲートの基本性質の証明 (De Morgan 則など) | ⬜ 未着手 |
| 1-3-9 | Simulated Buildings (シミュレーション装置) 全種の定義 | ⬜ 未着手 |

---

## フェーズ 2: 加工フローの表現

単体の装置だけでなく、装置を接続した「加工フロー」を Lean で表現し、入出力を計算できるようにする。

### 2-1. Shape Processing フローの表現

| # | タスク | 状態 |
|---|---|---|
| 2-1-1 | 加工装置を接続するグラフ / パイプライン型の設計 | ⬜ 未着手 |
| 2-1-2 | フローの評価関数の実装 (入力シェイプ → 出力シェイプ) | ⬜ 未着手 |
| 2-1-3 | 代表的な加工フロー (例: 切断 → 回転 → 切断 による象限分解) の表現と検証 | ⬜ 未着手 |
| 2-1-4 | フロー等価性の定義と証明補助 | ⬜ 未着手 |

### 2-2. Wires and Logic フローの表現

| # | タスク | 状態 |
|---|---|---|
| 2-2-1 | 論理信号を伝達するワイヤーネットワーク型の設計 | ⬜ 未着手 |
| 2-2-2 | ワイヤーネットワークの評価関数の実装 (入力信号 → 出力信号) | ⬜ 未着手 |
| 2-2-3 | 代表的なワイヤー回路 (例: 比較ゲートによる条件分岐) の表現と検証 | ⬜ 未着手 |

---

## フェーズ 3: MAM (Make Anything Machine) の表現

### 3-1. ワイヤー系装置によるフロー制御との連携

| # | タスク | 状態 |
|---|---|---|
| 3-1-1 | **Belt Filter** / **Pipe Gate** によるシェイプ・液剤のフロー制御を加工フローと統合 | ⬜ 未着手 |
| 3-1-2 | 信号によって動的に変化する加工フロー (条件付き加工) の表現 | ⬜ 未着手 |
| 3-1-3 | **Operator Shape Receiver** (オペレーター図形レシーバー) の定義 | ⬜ 未着手 |

### 3-2. 既存 MAM の形式化・検証

| # | タスク | 状態 |
|---|---|---|
| 3-2-1 | 既知の MAM 設計を Lean で記述 | ⬜ 未着手 |
| 3-2-2 | MAM の出力シェイプをゲーム内挙動と照合・一致確認 | ⬜ 未着手 |
| 3-2-3 | 任意の無着色 1 レイヤシェイプを製造できることの証明 | ⬜ 未着手 |

### 3-3. MAM 設計支援

| # | タスク | 状態 |
|---|---|---|
| 3-3-1 | ある MAM が生成可能なシェイプの集合 (表現能力) を算出する関数の実装 | ⬜ 未着手 |
| 3-3-2 | 目標シェイプを入力として加工手順を逆算するソルバーの実装 | ⬜ 未着手 |
| 3-3-3 | ソルバー出力の健全性 (求められた手順を実行すると目標シェイプが得られること) の証明 | ⬜ 未着手 |

---

## 凡例

| 記号 | 意味 |
|---|---|
| ✅ 完了 | 実装・検証済み |
| 🔄 進行中 | 現在作業中 |
| ⬜ 未着手 | まだ開始していない |
| ⏸ 保留 | 依存関係・方針待ちなどで一時停止中 |

---

## Appendix ツールチェイン整備計画

証明計画とは独立した、エージェント支援・開発基盤の整備項目。

| # | 整備項目 | 優先 | 概要 |
|---|---|---|---|
| T-1 | `lean-mathlib-search` スキルの新設 | ✅ 完了 | SKILL.md・`lean-lemma-finder` エージェント・`references/` (mathlib-search-guide.md, batteries-catalog.md) を整備済み。`#leansearch` / `#loogle` / `exact?` / `apply?` の4段階パイプライン・命名規則予測・Fin/Iff ゴールパターンを収録。 |
| T-2 | S2IL 補題インデックスの整備 | 中→**高** | `docs/lean/s2il-lemma-index.md` を新設。`gravity-proof-cheatsheet.md` 廃止に伴いその内容を吸収。詳細: [gravity-proof-execution-plan.md](gravity-proof-execution-plan.md) Wave 0 (0-1〜0-5) |
| T-3 | 等変性・交換則証明パターン集の拡充 | 中→**高** | `docs/knowledge/equivariance-proof-patterns.md` を新設し、既存の個別 knowledge を統合。詳細: [gravity-proof-execution-plan.md](gravity-proof-execution-plan.md) Wave 0 (0-6〜0-9) |
| T-4 | `lean-mathlib-search` — `lean-lsp-mcp` 統合評価 | 低 | MCP ツール `lean_state_search` 等を用いた REPL 不要の補題検索と既存フローの比較・移行判断。REPL は現在デフォルトモードで全 Mathlib タクティク・検索操作が利用可能（`-NoPickle` ~60s の制約は解消済み）なので優先度は低い（要 MCP サーバー導入評価）。 |
| T-5 | `batteries-catalog.md` の継続的更新フロー整備 | 低 | `lean-lemma-finder` で新補題を発見した際に `batteries-catalog.md` へ追記する運用を定着させる。Phase 2 以降で `List`・`Finset` 系補題が増えた時点で特に有効。`lean-proof-progress` スキルとの連携セッション終了チェックリストへの組み込みを検討。 |


### T-1 詳細: `lean-mathlib-search` スキル

> 旧 `docs/lean/repl-guide.md` の `[IDEA-1]` より移管。

現在 UC-8 として `#leansearch` / `#loogle` / `exact?` / `apply?` の使い方を `repl-guide.md` に収録しているが、
Mathlib 補題の探索が証明作業の主要ボトルネックになる段階（`stack_rotate180_comm` 等、`List`・`Finset`・`Nat` 系補題を大量に必要とするフェーズ）では、
専用スキル `.github/skills/lean-mathlib-search/SKILL.md` を設けて以下を体系化することを検討する。

- クエリ生成ガイド（ゴール状態 → 自然言語クエリへの変換パターン）
- `#leansearch` / `#loogle` / `exact?` / `apply?` の優先順位と使い分けフロー
- `mathlib-reference-guide.md` との連携（分野別 API 索引の活用方法）
- 外部 MCP（`lean-lsp-mcp` の `lean_state_search` 等）との機能比較と移行基準
