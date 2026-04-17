# コードベース分割単位見直し計画

作成日: 2026-04-15
最終更新: 2026-04-17（v3 最終確定）

> この資料はドラフト版であり、今後の実装・検証に応じて構成や方針を更新する。

## 目的

S2IL の現行構成は `Behavior/` に加工操作と証明責務が集中しており、以下の問題が顕在化している。

- ドメイン分類が広すぎ、加工操作・加工装置の増加に対して階層が粗い
- 等変性・可換性・不変量などの「性質ベースの知識」が各所に分散する
- 巨大ファイルの読解・修正コストが局所的に高い（Gravity 系で ~7,000 行超）
- エージェントが探索時に「加工操作軸」と「性質軸」を行き来しづらい

本計画は、数学的美しさを最優先しつつ、コード的美しさと将来拡張性を両立する分割案を比較検討するための土台を提供する。

## 現行コードベースの定量プロファイル

計画の妥当性を具体的に評価するため、現行の定量プロファイルを以下に示す。

| 指標 | 値 |
|---|---|
| `.lean` 総行数 | ~16,100 行（S2IL/ 配下） |
| ファイル数 | 35 ファイル |
| Gravity 系合計 | ~7,700 行（6 ファイル、全体の 48%） |
| 1,000 行超ファイル | 4 ファイル（PermInvariance 2,273 / CommExt 1,991 / GroundedPlacement 1,912 / Equivariance 1,807） |
| sorry 数 | 0 |
| axiom 数 | 5 |
| 裸 simp | 0 |

### 現行ファイル規模上位（移行候補の優先指標）

| ファイル | 行数 | 責務 | 依存される数 |
|---|---|---|---|
| Gravity/PermInvariance_obsolated | 2,273 | settle_foldl_eq, バブルソート帰納法, spb 相互排除 | 1（内部） |
| Gravity/CommExt_obsolated | 1,991 | placeQuarter/settleStep 可換性, spb 拡張性 | 1（内部） |
| SettledState/GroundedPlacement | 1,912 | one_step_all_grounded, 配置ステップ接地保存 | 1 |
| Gravity/Equivariance_obsolated | 1,807 | r180/rCW 等変性基盤, BFS 等変性, Finset 等変性 | 1（内部） |
| Gravity/Defs | 657 | コア定義: BFS, 落下単位, ソート, 配置, process | 5（全 Gravity 系） |
| Gravity_obsolated (facade) | 644 | Bridge 補題, process_rotate180/CW, Shape 公開 API | 7 |
| CrystalBond | 587 | 結合判定, BFS, r180/rCW 等変性 | 2（Shatter, Gravity/Defs） |
| GenericBfs | 565 | 汎用 BFS 定義・帰納法基盤 | 2（CrystalBond, Gravity/Defs） |
| Shatter | 542 | 砕け散り処理, r180/rCW 等変性 | 3（Stacker, Cutter, PinPusher） |

### 現行 import 依存関係マップ

```
Shape 層（基盤）
  Color ← Quarter ← Layer ← QuarterPos ← Shape ← GameConfig ← Arbitrary

演算基盤層
  GenericBfs                              （import なし）
  Rotate                                  ← Shape
  Rotate180Lemmas                         ← QuarterPos, Rotate
  CrystalBond                             ← QuarterPos, Rotate, Rotate180Lemmas, GenericBfs

Gravity 層（最大依存ハブ）
  Gravity/Defs                            ← CrystalBond, GenericBfs, Rotate180Lemmas
  Gravity/Equivariance_obsolated          ← Gravity/Defs
  Gravity/CommExt_obsolated               ← Gravity/Equivariance_obsolated
  Gravity/PermInvariance_obsolated        ← Gravity/CommExt_obsolated
  Gravity/FoldlBridge_obsolated           ← Gravity/PermInvariance_obsolated (via SettleFoldlEq)
  Gravity_obsolated (facade)              ← SettleFoldlEq + FoldlBridge
  Gravity.lean (public facade)            ← Gravity_obsolated

Shatter 層
  Shatter                                 ← CrystalBond, Gravity, Rotate, Rotate180Lemmas

加工操作層
  Stacker                                 ← Gravity, Shatter, SettledState, GameConfig
  Cutter                                  ← Gravity, Shatter, Rotate, SettledState
  PinPusher                               ← Gravity, Shatter, Stacker, SettledState, GameConfig
  Painter                                 ← Shape, Rotate
  CrystalGenerator                        ← Shape, Rotate
  ColorMixer                              ← Color

SettledState 層（※ 全ファイルが Gravity に直接依存）
  SettledState/Core                           ← Gravity
  SettledState/Paint                          ← Gravity, Painter, CrystalGenerator, Rotate
  SettledState/Crystallize                    ← Gravity, CrystalGenerator
  SettledState/Rotate                         ← Gravity, Rotate
  SettledState/GroundedCore                   ← Gravity
  SettledState/GroundedInvariant              ← Gravity
  SettledState/GroundedPlacement              ← Gravity, GroundedCore, GroundedInvariant
  SettledState/GravityBridge                  ← Gravity, GroundedCore, GroundedInvariant, GroundedPlacement
  SettledState.lean (coordinator)          ← 全 SettledState/*

統合層
  SettledShape                             ← SettledState, PinPusher, Stacker, Cutter, Arbitrary
  Machine                                 ← Painter, CrystalGenerator, Rotate, PinPusher, Stacker, Cutter, ColorMixer, SettledShape
```

## 評価軸

評価は次の 5 軸で行う。

1. **拡張性**: 新しい装置・操作・証明が追加された際の増築容易性
2. **数学的美しさ**: 補題再利用、抽象化、証明チェーンの見通し
3. **コード的美しさ**: ファイル責務の単一性、命名/配置の一貫性
4. **エージェント負荷**: 探索・修正・影響範囲推定のしやすさ
5. **移行コスト**: 既存 import 変更、依存切り分け、段階導入の難易度

## 分割案サマリ

| 案 | 中心思想 | 拡張性 | 数学的美しさ | コード的美しさ | エージェント負荷 | 移行コスト |
|---|---|---|---|---|---|---|
| A ×不採用 | ドメイン縦割り（操作種別） | 高 | 中 | 高 | 低 | 中 |
| B ×不採用 | 性質横割り（等変性・不変量） | 中 | 高 | 中 | 中〜高 | 高 |
| C ×不採用 | 機械バーティカルスライス（装置単位） | 高 | 中 | 中〜高 | 低〜中 | 中〜高 |
| **D** | **二層ハイブリッド（下層理論 + 上層加工操作）** | **最高** | **高** | **最高** | **中** | **高** |

> **v3 最終確認（2026-04-17）**: 代替案の網羅的検討（依存深度別層化・三層分離・フラット名前空間・証明ライブラリ分離）を実施し、案 D が最善であることを確認した。詳細は「§ 代替案の網羅的検討」を参照。v2 からの主要変更は SettledState の Kernel → Operations 移動（依存関係の実態反映、下記 v3 改訂を参照）。

### 評価の補足・修正点（v2 見直し）

旧版で案 B の数学的美しさを「最高」としていたが、現行コードベースの証明チェーンを精査した結果、以下の点で「高」に修正した。

- 案 B（性質横割り）は抽象的には最も数学的に美しいが、S2IL の証明チェーンは「Gravity 定義 → 等変性 → 可換性 → ソート不変性 → Bridge → 公開 API」という**線形の依存連鎖**を持つ。性質横割りではこの連鎖が `Equivariance/` と `Invariants/` と `Operations/` を横断し、証明の読解・追跡が困難になる
- 案 C の拡張性を「最高」から「高」に修正。装置単位の閉包は確かに増築に有利だが、共通理論（BFS 健全性、Finset 等変性等）を重複なく管理するには共有層の設計が必要であり、無条件に最高とは言えない
- 案 D の数学的美しさは、Kernel 層に共通理論を集約しつつ、Gravity のような長大な線形チェーンを Operation 内でまとまりよく保持できる点で「高」が妥当

## 各案の特徴

### 案D: 二層ハイブリッド（推奨）

- 下層（Kernel）で共通理論、上層（Operations）で加工操作別 API/定義を整理する
- 数学的抽象と実装可読性のバランスが最も良い
- 初期移行コストは高いが、長期保守性が高い

#### 具体ディレクトリ構成（v3 最終版）

v2 で Kernel/Settled/ に配置していた SettledState を Operations/Settled/ に移動した。理由は「v3 改訂: SettledState の Operations 移動」を参照。

```text
S2IL/
  Kernel/                          -- 共通理論（Gravity 非依存の横断基盤）
    BFS/                           -- 汎用 BFS 定義・帰納法テンプレート
      GenericBfs.lean              ← 現 GenericBfs.lean（565 行）
    Bond/                          -- 結合判定・クラスタ計算
      CrystalBond.lean             ← 現 CrystalBond.lean（587 行）
    Transform/                     -- 回転・対称性変換の補題群
      Rotate.lean                  ← 現 Rotate.lean（183 行）
      Rotate180Lemmas.lean         ← 現 Rotate180Lemmas.lean（238 行）
  Operations/                      -- 加工操作別モジュール
    Gravity/                       -- 落下処理（最大モジュール）
      Defs.lean                    ← 現 Gravity/Defs.lean（657 行）
      Equivariance.lean            ← 現 Gravity/Equivariance_obsolated.lean（1,807 行）
      CommExt.lean                 ← 現 Gravity/CommExt_obsolated.lean（1,991 行）
      PermInvariance.lean          ← 現 Gravity/PermInvariance_obsolated.lean（2,273 行）
      FoldlBridge.lean             ← 現 Gravity/FoldlBridge_obsolated.lean（334 行）
      Facade.lean                  ← 現 Gravity_obsolated.lean（644 行）
    Settled/                       -- 安定状態の定義・判定・保存証明（全ファイル Gravity 依存）
      Core.lean                    ← 現 SettledState/Core.lean（120 行）
      Paint.lean                   ← 現 SettledState/Paint.lean（270 行）
      Crystallize.lean             ← 現 SettledState/Crystallize.lean（106 行）
      Rotate.lean                  ← 現 SettledState/Rotate.lean（36 行）
      GravityBridge.lean           ← 現 SettledState/GravityBridge.lean（37 行）
      GroundedCore.lean            ← 現 SettledState/GroundedCore.lean（395 行）
      GroundedInvariant.lean       ← 現 SettledState/GroundedInvariant.lean（269 行）
      GroundedPlacement.lean       ← 現 SettledState/GroundedPlacement.lean（1,912 行）
    Shatter/
      Shatter.lean                 ← 現 Shatter.lean（542 行）
    Painter/
      Painter.lean                 ← 現 Painter.lean（88 行）
    CrystalGenerator/
      CrystalGenerator.lean        ← 現 CrystalGenerator.lean（87 行）
    Cutter/
      Cutter.lean                  ← 現 Cutter.lean（424 行）
    Stacker/
      Stacker.lean                 ← 現 Stacker.lean（269 行）
    PinPusher/
      PinPusher.lean               ← 現 PinPusher.lean（218 行）
    ColorMixer/
      ColorMixer.lean              ← 現 ColorMixer.lean（21 行）
  Shape/                           -- シェイプ定義（現行通り）
    （変更なし）
  Machine/                         -- 加工装置ラッパー（現行通り）
    Machine.lean
  SettledShape.lean                -- 統合型（SettledState + 操作の糊）
```

#### v3 構成の設計根拠

1. **Kernel は「Gravity 非依存の横断基盤」に厳格限定**: BFS・Bond・Transform の 3 サブディレクトリのみ。v2 で Kernel に配置していた Settled を Operations に移動した（理由は下記 v3 改訂を参照）
2. **Operations/Gravity/ は線形チェーンをそのまま保持**: Gravity の証明は `Defs → Equivariance → CommExt → PermInvariance → FoldlBridge → Facade` の 6 段線形チェーン。この構造を Operations/Gravity/ 内に閉じ込めることで、証明の読解性を維持する
3. **`_obsolated` サフィックスの除去**: 移行完了後は `_obsolated` を外し、正式名称に統一する
4. **SettledState は Operations/Settled/ へ**: v3 改訂で Kernel から移動（下記参照）
5. **小規模操作はフラットで十分**: Painter（88 行）、ColorMixer（21 行）等は単一ファイルで十分だが、ディレクトリの統一性のため Operations/X/ に配置する。将来の等変性証明追加時にファイル追加が自然にできる

#### v3 改訂: SettledState の Operations 移動

v2 では SettledState を Kernel/Settled/ に配置していたが、import 依存の精査（v3）により以下が判明した。

**事実**: SettledState の **全 8 ファイルが Gravity を直接 import** している。

| ファイル | Gravity 依存 | 補足 |
|---|---|---|
| Core.lean | ✅ 直接 import | `Gravity.groundedPositions` 等を使用 |
| Paint.lean | ✅ 直接 import | `IsSettled` 保存に Gravity 定義が必要 |
| Crystallize.lean | ✅ 直接 import | 同上 |
| Rotate.lean | ✅ 直接 import | `floatingUnits_isEmpty_rotateCW` を使用 |
| GroundedCore.lean | ✅ 直接 import | `Gravity.groundedPositions` で定義 |
| GroundedInvariant.lean | ✅ 直接 import | 接地不変量の証明 |
| GroundedPlacement.lean | ✅ 直接 import | 配置ステップの接地保存 |
| GravityBridge.lean | ✅ 直接 import | Gravity foldl ロジックの橋渡し |

v2 の配置（Kernel/Settled/）では Kernel → Operations/Gravity/ という**上向き依存**が発生し、「Kernel は下層基盤」という階層原則に違反する。

**移動の判断根拠**:

1. **階層原則の遵守**: Kernel が Operations に依存しないことで、Kernel は真に独立した基盤層として機能する
2. **意味論的正当性**: `IsSettled` は「Gravity 適用後に形状が変化しない」状態を意味する。これは本質的に Gravity の概念であり、Operations 層に属するのが自然
3. **Kernel の簡素化**: Kernel は ~1,573 行（BFS 565 + Bond 587 + Transform 421）に縮小。軽量で依存なしの純粋な共通基盤となる
4. **依存フローの明確化**: Operations 内の依存フローは `Gravity/ → Settled/ → {Stacker/, Cutter/, PinPusher/}` と線形で、追跡が容易

**v2 の Kernel 配置を支持していた「将来の再利用性」引数について**: `AllNonEmptyGrounded` / `ImmBelow` が他の操作にも適用可能という議論はあったが、現時点で全定義が Gravity に直接依存しており、抽象化が成立していない。将来 Gravity 非依存の接地概念が必要になった場合は、その時点で Kernel/Grounding/ を新設するのが適切。

#### 現行構成との差分概要

| 変更種別 | 対象 | 変更内容 | 影響行数 |
|---|---|---|---|
| ディレクトリ移動 | Behavior/GenericBfs → Kernel/BFS/ | パス変更のみ | ~565 |
| ディレクトリ移動 | Behavior/CrystalBond → Kernel/Bond/ | パス変更のみ | ~587 |
| ディレクトリ移動 | Behavior/Rotate* → Kernel/Transform/ | パス変更のみ | ~421 |
| ディレクトリ移動 | Behavior/Gravity/* → Operations/Gravity/ | パス変更 + `_obsolated` 除去 | ~7,714 |
| ディレクトリ移動 | Behavior/SettledState/* → Operations/Settled/ | パス変更のみ | ~3,145 |
| ディレクトリ移動 | Behavior/{Shatter,Painter,...} → Operations/*/ | パス変更のみ | ~1,649 |
| import 更新 | 全ファイル | namespace 変更に伴う import 書き換え | ~35 ファイル |
| re-export ハブ | 新規 Kernel.lean, Operations.lean | 移行期の互換 import | 新規 ~50 行 |

## 推奨方針

現時点の推奨は **案D（二層ハイブリッド）**。v3 で最終確定とする。

理由:

1. Gravity 非依存の共通理論を Kernel 層に集約し、純粋な下層基盤を維持できる
2. 加工操作別 API は Operations 層で追えるため実装可読性を維持できる
3. エージェント探索を「加工操作起点 → 共通理論」の 2 段導線に統一できる
4. Gravity の線形証明チェーン（6 段）を Operations/Gravity/ 内に閉包できる
5. SettledState が Operations/Settled/ にあることで、Gravity → Settled → {Stacker, Cutter, PinPusher} の依存フローが明瞭
6. Wave Gravity Model（§3 gravity-proof-execution-plan.md）移行時に Operations/Gravity/ の内部構造だけを変更すれば済む

## 段階導入プラン（案Dを目標）

### 前提条件

- 各 Phase の着手前に `lake build` が `errors = 0` であること
- Phase 間は独立コミット可能な粒度で区切る
- 移行中は旧パスからの re-export で互換性を維持する

### Phase 0: 依存可視化・準備（短期）

**目的**: 移行の前提情報を揃え、リスクを可視化する。

#### 作業項目

| # | 作業 | 成果物 | 推定工数 |
|---|---|---|---|
| 0-1 | `lake exe depgraph` で現行の定理依存グラフを出力 | `docs/plans/dep-graph-baseline.json` | 0.5h |
| 0-2 | 巨大ファイルの責務分解候補を列挙 | 本ドキュメントの定量プロファイル（完了） | — |
| 0-3 | 移行対象の優先順位付け | 下表の優先順位表 | 0.5h |
| 0-4 | import 書き換えの影響行数を概算 | 各 Phase の概算コード変更量（本セクション） | — |

#### 移行対象の優先順位

| 優先度 | モジュール群 | 理由 |
|---|---|---|
| **High** | Gravity/* → Operations/Gravity/ | 最大モジュール（7,700 行）。`_obsolated` 除去による可読性向上が即効性あり |
| **High** | SettledState/* → Operations/Settled/ | 全ファイルが Gravity 依存。Operations 層に配置して階層原則を維持 |
| **Medium** | GenericBfs, CrystalBond → Kernel/ | 2+ 操作から参照される共通基盤 |
| **Medium** | Rotate, Rotate180Lemmas → Kernel/Transform/ | 等変性証明の共通基盤 |
| **Low** | Painter, CrystalGenerator, ColorMixer → Operations/ | 小規模・低依存。移行効果は小さいが統一性のため |

#### 完了条件

- 依存グラフが JSON 出力され、主要モジュールの依存方向が文書化されている
- 移行対象の優先順位（High/Medium/Low）が付与されている
- 概算コード変更量が Phase 別に見積もられている

### Phase 1: Kernel 層の先行抽出（短中期）

**目的**: 横断再利用される Gravity 非依存の共通理論を `Kernel/` に移設し、下層基盤を確立する。

#### 作業項目

| # | 作業 | 対象ファイル | import 変更数 | 推定行数変更 |
|---|---|---|---|---|
| 1-1 | `GenericBfs.lean` → `Kernel/BFS/GenericBfs.lean` | 1 ファイル移動 | 2 箇所（CrystalBond, Gravity/Defs） | ~5 行 |
| 1-2 | `CrystalBond.lean` → `Kernel/Bond/CrystalBond.lean` | 1 ファイル移動 | 2 箇所（Shatter, Gravity/Defs） | ~5 行 |
| 1-3 | `Rotate.lean` + `Rotate180Lemmas.lean` → `Kernel/Transform/` | 2 ファイル移動 | ~8 箇所 | ~16 行 |
| 1-4 | `Kernel.lean` re-export ハブ作成 | 新規 | — | ~15 行（新規） |
| 1-5 | 旧パスに re-export スタブ作成 | ~4 ファイル | — | ~8 行（新規） |
| 1-6 | `S2IL.lean` の import 更新 | 1 ファイル | — | ~10 行 |
| 1-7 | `lake build` 全体ビルド検証 | — | — | — |

#### 概算コード変更量

- **移動**: ~1,573 行（4 ファイルのパス変更。内容変更なし）
- **import 書き換え**: ~30 行（import 文の namespace 更新）
- **新規**: ~25 行（re-export ハブ + スタブ）
- **リスク**: 低（全ファイルが Gravity 非依存のため循環リスクなし）

#### 実施順序（依存関係の逆順）

1. GenericBfs（依存元なし → 最も安全）
2. Rotate, Rotate180Lemmas（GenericBfs に依存しない）
3. CrystalBond（GenericBfs, Rotate180Lemmas に依存）

#### 完了条件

- `Kernel/{BFS,Bond,Transform}/` に各ファイルが配置されている
- 少なくとも 2 つの加工操作が `Kernel/` を参照している
- 旧パスからの re-export が機能し、全体ビルドが通る

### Phase 2: Operations 層の構築（中期）

**目的**: 加工操作モジュールと SettledState を `Operations/` に移設し、`_obsolated` サフィックスを除去する。

#### 作業項目

| # | 作業 | 対象ファイル | import 変更数 | 推定行数変更 |
|---|---|---|---|---|
| 2-1 | `Gravity/*` → `Operations/Gravity/` + `_obsolated` 除去 | 7 ファイル移動 + リネーム | ~10 箇所 | ~20 行 |
| 2-2 | `SettledState/*` → `Operations/Settled/` | 8 ファイル移動 | ~6 箇所 | ~12 行 |
| 2-3 | `Shatter.lean` → `Operations/Shatter/` | 1 ファイル移動 | 3 箇所 | ~6 行 |
| 2-4 | `Stacker.lean` → `Operations/Stacker/` | 1 ファイル移動 | 1 箇所 | ~2 行 |
| 2-5 | `Cutter.lean` → `Operations/Cutter/` | 1 ファイル移動 | 1 箇所 | ~2 行 |
| 2-6 | `PinPusher.lean` → `Operations/PinPusher/` | 1 ファイル移動 | 1 箇所 | ~2 行 |
| 2-7 | `Painter.lean` + `CrystalGenerator.lean` + `ColorMixer.lean` → `Operations/` | 3 ファイル移動 | 1 箇所 | ~6 行 |
| 2-8 | `Operations.lean` re-export ハブ作成 | 新規 | — | ~25 行（新規） |
| 2-9 | 旧 `Behavior/` パスに re-export スタブ作成 | ~21 ファイル | — | ~42 行（新規） |
| 2-10 | `SettledShape.lean` の import 更新 | 1 ファイル | — | ~10 行 |
| 2-11 | `Machine.lean` の import 更新 | 1 ファイル | — | ~10 行 |
| 2-12 | `S2IL.lean` の import 更新 | 1 ファイル | — | ~15 行 |
| 2-13 | `lake build` 全体ビルド検証 | — | — | — |

#### 実施順序（依存関係の逆順）

1. Gravity/*（SettledState が依存 → 先に移動して import を確定）
2. SettledState/*（Gravity 移動後に実施。import 先が Operations/Gravity/ に確定済み）
3. Shatter（Gravity に依存）
4. Stacker, Cutter, PinPusher（Gravity + SettledState に依存）
5. Painter, CrystalGenerator, ColorMixer（独立性が高い）

#### 概算コード変更量

- **移動**: ~11,850 行（22 ファイルのパス変更 + リネーム。内容変更は `_obsolated` 除去のみ）
- **import 書き換え**: ~130 行（import 文の namespace 更新。Gravity 系は内部 import も変更、SettledState 系は Gravity 参照先を更新）
- **新規**: ~70 行（re-export ハブ + スタブ）

#### `_obsolated` サフィックス除去の安全性

- Gravity 系ファイルの `_obsolated` は歴史的経緯で付与されたもの。ファイル移動と同時にリネームすることで、git の rename detection が効きやすくなる
- 内部 import の `Gravity.Equivariance_obsolated` → `Operations.Gravity.Equivariance` 等の一括置換は PowerShell の `-creplace` で機械的に実施可能

#### 完了条件

- `Operations/` 配下に全加工操作が配置されている
- `_obsolated` サフィックスが全て除去されている
- import パス移行後も全体ビルドが通る
- 探索導線（README/インデックス）が更新されている

### Phase 3: 収束・最適化（中長期）

**目的**: 旧構成の互換層を削減し、新階層を唯一の正とする。

#### 作業項目

| # | 作業 | 推定行数変更 |
|---|---|---|
| 3-1 | 旧 `Behavior/` re-export スタブの削除 | ~50 行削除 |
| 3-2 | 旧 `Behavior/` ディレクトリの削除 | ディレクトリ削除 |
| 3-3 | `S2IL.lean` を最終 import 構成に更新 | ~10 行 |
| 3-4 | `s2il-lemma-index.md` のファイル構造マップ更新 | ~200 行 |
| 3-5 | 命名規約ドキュメント（AGENTS.md 等）の更新 | ~20 行 |
| 3-6 | Test/ 配下の import 更新 | ~20 ファイル |
| 3-7 | Verification/ 配下の import 更新 | ~5 ファイル |
| 3-8 | `lake build` 全体ビルド + 全テスト実行 | — |

#### 概算コード変更量

- **削除**: re-export スタブ ~50 行 + 旧ディレクトリ
- **import 書き換え**: Test/ + Verification/ で ~50 行
- **docs 更新**: ~250 行

#### 完了条件

- 新階層を唯一の正として運用可能
- 旧 `Behavior/` ディレクトリが存在しない
- 全テスト・検証が通る

### Phase 全体の工数概算

| Phase | 推定工数 | 推定 import 変更行数 | リスク |
|---|---|---|---|
| Phase 0 | 1h | 0 | 低 |
| Phase 1 | 1-2h | ~30 行 | 低（全ファイル Gravity 非依存、循環リスクなし） |
| Phase 2 | 3-4h | ~130 行 | 中（Gravity 系 `_obsolated` 一括リネーム + SettledState 移動） |
| Phase 3 | 1-2h | ~50 行 | 低（互換層削除のみ） |
| **合計** | **6-9h** | **~210 行** | — |

### Wave Gravity Model 移行との関係

案 D の段階導入と Wave Gravity Model（gravity-proof-execution-plan.md §3）は以下のように連携する。

| 実施順序 | 方針 | 理由 |
|---|---|---|
| **案 D 先行** → Wave Model 後 | ✅ 推奨 | Operations/Gravity/ 内部構造のみ変更すればよく、Kernel 層は影響なし。`_obsolated` 除去後のクリーンな状態で Wave Model を実装できる |
| Wave Model 先行 → 案 D 後 | △ 可能 | Wave Model で Gravity 内部が大きく変わると、移行時の diff が複雑化する |
| 同時実施 | × 非推奨 | import 変更と証明構造変更が複合し、デバッグが困難 |

---

## 代替案の網羅的検討（v3 最終確認）

案 D を最終案とする前に、A/B/C 以外の代替アプローチを網羅的に検討した。

### 検討した代替案

| # | 案名 | 中心思想 | 棄却理由 |
|---|---|---|---|
| E | 依存深度別層化 | import 深度（Layer 0〜6）でディレクトリを分割 | 意味論的なグループ化がなく、「BFS と Rotate が同一ディレクトリ」のような非直感的配置が頻発。探索時に「この操作はどの深度？」という追加変換が必要になり、エージェント負荷が増大 |
| F | フラット名前空間 | ディレクトリ階層を浅くし、Lean namespace のみで論理構造を表現 | 移行コストは最小だが、ファイルシステム上の構造がなく探索導線が確立できない。エージェントの `includePattern` 指定が効かず、毎回全ファイル grep が必要 |
| G | 三層分離（Foundation / Theory / Operations） | Kernel を Foundation（型定義）と Theory（証明基盤）に分割 | Foundation は現行 Shape/ と重複し、Theory は Kernel のリネームに過ぎない。階層が 1 つ増えるだけで実質的なメリットなし |
| H | 証明ライブラリ分離 | 定義（Def/）と証明（Proof/）を完全分離 | 案 B の変形。Gravity の線形チェーンが Def/ と Proof/ に分断され、同一操作の証明を読むのに 2 ディレクトリを行き来する必要がある |
| I | Gravity 吸収型 | SettledState の Grounded* を Operations/Gravity/ に吸収し、残りを Kernel/Settled/ に | SettledState が 2 箇所に分散する。v3 精査で全 8 ファイルが Gravity 依存と判明したため、分割の根拠がなくなった |

### 案 D が最善である理由

1. **階層原則の純粋性**: Kernel（~1,573 行）は Gravity 非依存。上向き依存がゼロで、真の下層基盤として機能する
2. **線形チェーンの保全**: Gravity の 6 段線形チェーンが Operations/Gravity/ 内に完全に閉包される。案 B/E/H はこのチェーンを分断する
3. **依存フローの単純性**: `Kernel → Operations/Gravity/ → Operations/Settled/ → {Stacker, Cutter, PinPusher}` の一方向フロー。循環や上向き依存がない
4. **移行コストの現実性**: 既存ファイルの内容変更は `_obsolated` 除去のみ。import パス書き換えは機械的に実施可能
5. **拡張の自然さ**: 新操作追加時は `Operations/NewOp/` を追加するだけ。Kernel の変更不要

---

## Appendix A: 案D向けエージェント負荷低減機構（エージェント専用）

本 Appendix は人間向け導線ではなく、エージェント専用の実行基盤として定義する。
目的は「探索の初手を固定し、コンテキスト消費を最小化し、修正影響の推定を機械的に行う」こと。

### 設計原則

1. **既存インフラとの重複を避ける**: `s2il-lemma-index.md` や `depgraph` ツールと機能が重なる機構は統合・代替する
2. **ROI 重視**: 保守コストに見合うコンテキスト削減効果がある機構のみ採用する
3. **段階的導入**: 全機構を一度に導入せず、効果測定しながら追加する
4. **機械読取安定性**: 人間可読性より、エージェントの構造化パーサで安定的に読み取れる形式を優先する

### A-1. `S2IL/_agent/` 配置方針

結論: `S2IL/_agent/` に配置する。

根拠:

1. `lake build` は `.lean` import のみ解決するため、`.json` / `.jsonl` / `.yaml` はビルド対象外
2. エージェント検索時は `includePattern` を `.lean` に限定すればノイズ回避可能
3. コードと物理的に近接することで、更新漏れのリスクを低減できる

運用ガード:

1. `S2IL/_agent/` 内ファイルは `.gitignore` に含めない（リポジトリで共有する）
2. 生成物には `"generated": true` フラグを持たせ、手編集領域と区別する
3. エージェント検索時は `includePattern = "**/*.lean"` を原則とする

### A-2. 機構候補の再評価

旧版の 7 機構を現行コードベースの実態に照らして再評価し、ROI に基づいて 3 段階（即効・中期・長期）に分類した。

#### 即効（Phase 0-1 で導入）

| ID | 機構 | 配置 | 目的 | ROI 根拠 |
|---|---|---|---|---|
| **M1** | ルートグラフ | `S2IL/_agent/route-map.json` | 操作起点の読取順を固定 | 毎回の探索初動で 2-3 回の grep を削減。保守コスト低（import 変更時のみ更新） |
| **M5** | 実行レシピ | `S2IL/_agent/query-playbook.json` | タスク種別ごとの探索定型化 | 高頻度タスク 5 種を定型化するだけで、新規セッション開始時の探索コストを ~50% 削減 |

#### 中期（Phase 2 で導入）

| ID | 機構 | 配置 | 目的 | ROI 根拠 |
|---|---|---|---|---|
| **M2** | シンボル位置 DB | `S2IL/_agent/symbol-map.jsonl` | 定理/def の最短到達 | Gravity 系 7,700 行からの定理検索を O(1) 化。ただし `depgraph --json` と重複するため、depgraph の出力形式を拡張する方が効率的 |
| **M3** | 安定 re-export ハブ | `Kernel.lean`, `Operations.lean` | import 分岐の削減 | Phase 1-2 で自然に生成されるため、追加コストなし |

#### 長期（Phase 3 以降で評価）

| ID | 機構 | 配置 | 判断 | 理由 |
|---|---|---|---|---|
| M4 | 変更影響ルール DB | `S2IL/_agent/impact-map.yaml` | **保留** | import 依存グラフから機械的に導出可能。`depgraph` ツールの `--root` オプションで代替できるため、専用 DB の保守コストに見合わない可能性がある |
| M6 | サブエージェント契約 | `S2IL/_agent/subagent-contracts/` | **保留** | 現行の AGENTS.md + スキルで十分に機能している。契約の形式化は運用が安定してから判断する |
| M7 | スキル自動更新 | `.github/skills/*` + `generated/` | **保留** | symbol-map の半自動更新から着手し、安定後に拡張を判断する |

### A-3. 各機構の具体設計

#### M1. ルートグラフ

```json
{
  "version": 1,
  "description": "Operation-first reading order for agent exploration",
  "routes": {
    "Gravity": {
      "entry": "S2IL/Operations/Gravity/Facade.lean",
      "chain": [
        "S2IL/Operations/Gravity/Defs.lean",
        "S2IL/Operations/Gravity/Equivariance.lean",
        "S2IL/Operations/Gravity/CommExt.lean",
        "S2IL/Operations/Gravity/PermInvariance.lean",
        "S2IL/Operations/Gravity/FoldlBridge.lean"
      ],
      "kernel_deps": ["S2IL/Kernel/BFS/GenericBfs.lean", "S2IL/Kernel/Bond/CrystalBond.lean"]
    },
    "Cutter": {
      "entry": "S2IL/Operations/Cutter/Cutter.lean",
      "kernel_deps": ["S2IL/Kernel/Transform/Rotate.lean"],
      "ops_deps": ["S2IL/Operations/Settled/Core.lean"]
    }
  }
}
```

保守ルール:

- 新規モジュール追加時のみ差分更新（各操作最大 3 依存先）
- `route-map.json` の整合性は Phase 移行完了時に検証する

#### M5. 実行レシピ

```json
{
  "version": 1,
  "recipes": {
    "equivariance_add": {
      "description": "新しい等変性証明を追加する",
      "steps": [
        {"action": "read", "target": "S2IL/_agent/route-map.json", "extract": "routes.{operation}"},
        {"action": "grep", "pattern": "{transform}_comm", "scope": "S2IL/Operations/{operation}/"},
        {"action": "read", "target": "docs/s2il/equivariance-proof-patterns.md"},
        {"action": "template", "pattern": "パターン 1 or 2 を選択"}
      ],
      "stop_condition": "等変性パターンが特定され、証明骨格が構成できた時点"
    },
    "axiom_replace": {
      "description": "axiom を構成的証明に置換する",
      "steps": [
        {"action": "read", "target": "docs/plans/gravity-proof-execution-plan.md", "section": "§2"},
        {"action": "grep", "pattern": "axiom {name}", "scope": "S2IL/"},
        {"action": "read", "target": "依存先ファイル"}
      ]
    },
    "gravity_debug": {
      "description": "Gravity 関連のビルドエラーを修正する",
      "steps": [
        {"action": "read", "target": "S2IL/Operations/Gravity/Facade.lean"},
        {"action": "build", "target": "S2IL.Operations.Gravity.Facade"},
        {"action": "fix", "strategy": "error-fixer skill"}
      ]
    }
  }
}
```

#### M2. シンボル位置 DB（`depgraph` 統合案）

独立 DB として保守するのではなく、既存の `depgraph` ツールを拡張する方が保守コストが低い。

提案: `lake exe depgraph --symbol-map --json` オプションを追加し、以下の形式で出力する。

```jsonl
{"symbol": "process_rotate180", "kind": "theorem", "file": "S2IL/Operations/Gravity/Facade.lean", "line": 189, "tags": ["equivariance", "r180"]}
{"symbol": "shouldProcessBefore_no_mutual", "kind": "theorem", "file": "S2IL/Operations/Gravity/PermInvariance.lean", "line": 1480, "tags": ["dag", "spb"]}
```

メリット:

- `depgraph` はビルド環境の `Environment` API から直接抽出するため、常に正確
- 手動保守が不要（ビルドのたびに再生成可能）
- 既存ツールの拡張なので新規ツール導入のオーバーヘッドがない

### A-4. 採用パターン（簡素化版）

旧版の P1-P5 を簡素化し、Phase と連動する 3 段階に統合した。

| 段階 | 構成 | 導入タイミング | ねらい |
|---|---|---|---|
| **S1: 即効** | M1（ルートグラフ）+ M5（実行レシピ） | Phase 0-1 完了時 | 探索初動の固定化。コンテキスト消費 ~30% 削減 |
| **S2: 探索最適** | S1 + M2（depgraph 拡張）+ M3（re-export ハブ） | Phase 2 完了時 | 定理検索の O(1) 化。import 簡素化 |
| **S3: 評価後追加** | S2 + 必要に応じて M4/M6/M7 | Phase 3 安定後 | 実測データに基づく追加判断 |

### A-5. `s2il-lemma-index.md` の移行方針

| Phase | 方針 | 理由 |
|---|---|---|
| Phase 0-1 | **現行索引を維持**（S1 互換） | 移行中は旧パスの参照も残るため、索引が導線として機能する |
| Phase 2 | **索引を新パスに更新** | Operations/Kernel パスに合わせてファイル構造マップを書き換え |
| Phase 3 | **段階縮退を評価** | M2（depgraph 拡張）が安定していれば、索引のファイル構造マップを廃止し、確立済みの事実・テスト一覧のみを残す |

### A-6. 新規提案: エージェント探索プロトコルの標準化

機構の導入に加えて、エージェントの**探索手順自体を標準化**することで、機構がない段階でもコンテキスト消費を削減できる。

#### 標準探索プロトコル（案 D 移行後）

```
1. タスクの加工操作を特定 → route-map.json の entry ファイルを読む
2. entry ファイルの公開 API シグネチャを確認（~50 行）
3. 必要な内部詳細がある場合のみ chain を辿る（lazy exploration）
4. Kernel 層への到達は chain 経由 or kernel_deps 経由のみ（直接 grep しない）
5. 3,000 行超ファイルへの直接 grep は Explore サブエージェントに委譲
```

このプロトコルは `AGENTS.md` の「検索戦略」セクションに組み込むことで、スキル・機構とは独立に効果を発揮する。

---

## Appendix B: かつて検討に上がっていた分割案（不採用）

### B-1. 案B（性質横割り）

特徴:

- 等変性・不変量・順序不変などを横断層で一元化できる
- 証明の再利用率が上がり、補題探索効率が高い
- 実装の置き場が分散し、加工操作起点では追いづらくなる

不採用理由:

- S2IL の証明チェーンは線形依存（Defs → Equivariance → CommExt → PermInvariance）が支配的であり、性質横割りではこの線形構造が 3+ ディレクトリを横断してしまう
- 「等変性」ディレクトリに Gravity の r180 等変性と Shatter の r180 等変性が同居すると、Gravity の証明チェーンの読解時に Shatter のコードがノイズになる
- 数学的に美しい分類ではあるが、実装の可読性とエージェント探索効率の面で案 D に劣る

### B-2. 案C（機械バーティカルスライス）

特徴:

- 各装置単位で `Defs / Proofs / Equivariance / Tests` を同居しやすい
- 新装置追加時の変更範囲が局所化しやすい
- 共通理論の切り出しが不十分だと重複補題が増える

不採用理由:

- GenericBfs（565 行）や CrystalBond（587 行）は Gravity と Shatter の双方から参照されており、装置単位に閉じ込めると重複配置が必要になる
- SettledState 系の保存定理群が特定の装置に帰属しない（Paint/Crystallize/Rotate/Gravity すべてが参照）
- 案 D の Kernel/Operations 分離で共通理論の重複を回避しつつ装置単位のまとまりも維持できるため、案 C の利点は案 D に包含される

### B-3. 案A（ドメイン縦割り）

特徴:

- 実装者にとって最も直感的
- 依存方向を `Core -> Physics -> Operations -> Machine` に揃えやすい
- 等変性補題は再び加工操作ファイルへ分散しやすい

不採用理由:

- 案 D への段階移行の踏み台にはなれるが、A → D の 2 段階は import 変更を 2 重に要するため直接 D 移行を推奨
- `Physics/Gravity/` と `Operations/Gravity/` の境界が曖昧（Gravity は「物理的な落下」と「加工操作としての gravity」が不可分）
- 案 D の Kernel 層は案 A の Core + Physics を統合・精練したものであり、案 A を経由するメリットがない
