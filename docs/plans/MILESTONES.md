# マイルストーン チェックシート

Shapez2 in Lean (S2IL) の開発マイルストーンと達成状況を管理するチェックシートです。

> 最新のビルド状態・sorry 件数は [`S2IL/_agent/sorry-goals.md`](../S2IL/_agent/sorry-goals.md)（自動生成）を参照。

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
| 1-2-4 | 切断系操作の基本性質の証明 | ✅ 完了 | `eastHalf_westHalf_combine` ✅, `swap_self` ✅, `combineHalves_self` ✅, `cut_rotate180_comm` ✅ (≤5L), `stack_rotate180_comm` ✅ (≤5L + IsSettled 仮説付き, Plan B-1 で axiom 化により sorry 解消済み), `pinPush_rotate180_comm` ✅ (≤5L), `paint_rotate180_comm` ✅, `crystallize_rotate180_comm` ✅, `gravity_rotate180_comm` ✅ (≤5L), `gravity_rotateCW_comm` ✅ (≤5L), `halfDestroy_rotate180` ✅, `swap_rotate180_comm` ✅。**Wave 7: process_rotate180 は ≥6L で偽（反例確認済み）**。sorry 全件解消（Plan B-1, 2026-04-14）。詳細: [gravity-proof-execution-plan.md](gravity-proof-execution-plan.md) |

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

## フェーズ R: リファクタリング & 数学的正しさの検証（S1 完了後に実施）

S1 全 sorry 解消後に集中して実施する整理フェーズ。
複数の証明で浮上した技術的負債をまとめて解消する。

### R-1. 証明ライブラリの中間表現統一

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| R-1-1 | GroundedMono 層以下で `getDir ≠ Quarter.empty` と `isOccupied = true` の二重表現を統一する。基本単位を `getDir ≠ Quarter.empty` とし、`isOccupied` は `placeLDGroupsLandings` 定義など既存 API との境界のみで使用 | ✅ 完了 | 2026-04-23: `CommExt/PlaceGrounding.lean` の chain 補題 3 本 (`foldl_placeFU_*`, `placeLDGroups_*`) を `getDir ≠ empty` 形に統一。`placeLDGroups_landing_nonEmpty` で 2 回必要だった bridge 呼び出しが 0 回になった |
| R-1-2 | 統一判断に基づき `foldl_placeFU_isOccupied_mono` / `isOccupied_placeLDGroups_mono` 等を必要最小限まで整理（`getDir` 版のみ残す、または相互変換を `@[simp]` にする） | ✅ 完了 | 2026-04-23: chain 3 本を改名・getDir 版に一本化（`foldl_placeFU_getDir_ne_empty_mono` / `placeLDGroups_getDir_ne_empty_mono` / `foldl_placeFU_written_getDir_ne_empty`）。leaf の `isOccupied_placeQuarter_mono` / `isOccupied_placeFallingUnit_mono` は Bool 形のほうが自然なので isOccupied 形のまま維持 |

### R-2. bridge 補題の配置整理

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| R-2-1 | 汎用 bridge 補題 (`isOccupied ↔ getDir`, `getQuarter ↔ layers.getD`, etc.) を適切な上流レイヤに移動する。判定基準: 定義元ファイルと同階層 or 1 つ上のファイル | ✅ 完了 | 2026-04-23: `isOccupied_of_getDir_ne_empty` / `getDir_ne_empty_of_isOccupied` を `CommExt/PlaceGrounding.lean` L976 から `Operations/Gravity/Defs.lean` の `isOccupied` 定義直後（L800）へ昇格。併せて `isOccupied_iff_getDir_ne_empty`（iff 形の統合版）を追加 |
| R-2-2 | bridge 補題の分類ルールを `S2IL/AGENTS.md` に明文化（「汎用変換補題は操作固有ファイルに置かない」） | ✅ 完了 | 既に記載済（"補題の配置ルール（bridge / helper）" セクション）。R-2-1 の実施例を反映 |
| R-2-3 | 既存 `CommExt/` 配下の補題をレビューし、操作非依存のものを上流へ昇格 | ⬜ 未着手 | R-2-1 / R-2-2 完了後の整理 |

### R-3. 数学的正しさの再検証

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| R-3-1 | 主要補題群 (B1/B2/B3a/B3b/B4) の仮定を最小化する再検証。現在の仮定で余剰なものがあれば削る | ⬜ 未着手 | |
| R-3-2 | `plausible` / `lean-theorem-checker` で主要補題をバッチ検証し、カウンターエグザンプルが存在しないことを再確認 | ⬜ 未着手 | |
| R-3-3 | 残存 axiom (S2, S3) の除去計画を更新する | ⬜ 未着手 | S3 除去完了後に S2 は `rotate180_eq_rotateCW_rotateCW` 経由で 1 行導出 |

### R-4. ドキュメント整理

| # | タスク | 状態 | 備考 |
|---|---|---|---|
| R-4-1 | 完了済み sorry-card を `archive/` へ一括移動、README を整理 | ⬜ 未着手 | |
| R-4-2 | `docs/plans/*.md` の陳腐化したセクションを削除、シングルソース原則に沿わない箇所を整理 | ⬜ 未着手 | |

---

## 凡例

| 記号 | 意味 |
|---|---|
| ✅ 完了 | 実装・検証済み |
| 🔄 進行中 | 現在作業中 |
| ⬜ 未着手 | まだ開始していない |
| ⏸ 保留 | 依存関係・方針待ちなどで一時停止中 |

---

## 将来課題

### stress8 (maxLayers > 5) の等変性サポート

> 出典: [gravity-proof-execution-plan.md](gravity-proof-execution-plan.md) §3

現行の `layerCount ≤ 5` 仮説は vanilla4/5 でのみ有効。stress8（maxLayers=8）では PinPusher・Cutter 等の gravity 入力が ≤ 8L となり `gravity_rotate180_comm` の適用不可。IsSettled アプローチで解決可能な箇所もあるが、各装置の構造的特殊性の調査が必要。現時点では優先度外（ストレステスト専用）。

### gravity_IsSettled の layerCount ≤ 5 制約解消

`gravity_IsSettled` は ≥6L のシェイプに対して偽であることが判明した（2026-04-12 反例発見）。
現在は `h_lc : s.layerCount ≤ 5` 制約付きで定理を述べている。

**反例**: 6L シェイプ `L0=[--,--], L1=[--,cr], L2=[--,P], L3=[cr,P], L4=[cr,P], L5=[cr,cr]`
- gravity 出力: `[[--,cr],[cr,P],[cr,P],[cr,P]]` — 浮遊クラスタ(3) が残る → NOT settled
- 根本原因: foldl 中の pin 配置が水平接地接触を切断し、隣接方向の crystal が非接地に

**仕様書の矛盾**: `falling.md` §7.1「反復は不要」vs §10.4「繰り返される」。≥6L では §7.1 が偽。

**解消方針（2段階）**:
1. `Gravity.process` を反復方式に変更（foldl 1パス → iterate until `floatingUnits = []`）
2. 反復版に対する `gravity_IsSettled` を `layerCount` 制約なしで証明

**前提条件**: 反復版 gravity の等変性証明（`process_rotate180` 等）の再構築が必要。
等変性証明自体は `layerCount ≤ 5` 制約付きで完了済みだが、反復版では新たな帰納法パターンが必要。

### sorry #4b の完全解消

`one_step_all_grounded_pin` の pin 着地位置非空ケース (crystal→pin 上書き) の sorry。

**困難の源泉**: `foldl_grounded_induction` の `∀ obs'` パターンでは証明不可能。
理由: ANEG(obs) + crystal→pin → ANEG(obs') は任意の ANEG obs に対しては偽（12768/53218 failures）。
foldl の中間状態に限れば真（16/16 = 0 failures at 5L 2dir）だが、中間状態の構造的情報（FVT等）が必要。

**計算検証済みの事実**:
| 条件 | 結果 |
|---|---|
| ANEG + FVT → crystal→pin → ANEG | 0 failures (19878 tests, ≤5L 2dir) |
| FVT は foldl 不変量 | ❌ (base: 3424 fail, step: 4760 fail) |
| pin NE 時に FVT 成立 (foldl中) | ✅ (16/16 = 0 fail, 5L 2dir) |

**解消方針候補**:
1. `foldl_grounded_induction` を拡張し、foldl prefix 構造を追跡する stronger invariant (FVT at pin NE moments) を導入
2. `all_grounded_settle_foldl` を `foldl_grounded_induction` なしで直接証明し、各ステップの具体的構造を利用
3. gravity を反復方式に変更すれば、sorry #4b の構造自体が変わり、別のアプローチが可能に


