# Layer C-1: Shape Processing Flow 計画

- 作成日: 2026-05-05
- 最終更新: 2026-05-05
- ステータス: **設計ドラフト / Layer C-1 着手準備**
- スコープ: Shape Processing フロー、Belt / Pipe ストリーム、装置グラフ、抽象処理能力

---

## 0. 目的

Layer C-1 では、Layer A/B で定義済みの純粋な加工操作を、実際の加工ラインとして接続・評価できる形に持ち上げる。

本計画の中心は次の 4 点である。

| 観点 | 方針 |
|---|---|
| 接続構造 | 線形パイプラインに限定せず、DAG 形式の装置グラフを初期対象に含める |
| ストリーム | Belt 上の Shape と Pipe 上の Fluid を区別して扱う |
| 処理能力 | スループット / 容量 / 消費量を first-class な抽象概念として導入する |
| 数値 | 具体的な装置別スループット値・容量値・制約値はこの計画では確定しない |

具体的な数値やゲーム内制約は後続の調査フェーズで確定する。本計画では、その値を後から差し込める Lean 側の構造と証明ロードマップを定める。

---

## 1. 参照元と正本の分担

本計画は既存資料の重複説明を避け、次のように正本を分担する。

| 情報 | 正本 | Layer C-1 での扱い |
|---|---|---|
| プロジェクト全体の層構造 | [MILESTONES.md](MILESTONES.md) | C-1 の位置付けを継承する |
| Layer A/B のコード構造 | [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) | facade / Internal / MECE / 等変性規約を継承する |
| `GameConfig` | [../s2il/game-config.md](../s2il/game-config.md) | レイヤ上限の設定として維持し、処理能力設定とは混ぜない |
| ゲーム用語 | [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) | Belt / Pipe / Lane / Shape Processing の用語を再利用する |
| tick と Wave Gravity | [../shapez2/falling.md](../shapez2/falling.md) | 離散時間モデルの参考にする |
| 加工操作の Lean API | [../../S2IL/Operations.lean](../../S2IL/Operations.lean) | Flow 層から参照する唯一の Operations facade とする |
| Machine 統合層 | [../../S2IL/Machine.lean](../../S2IL/Machine.lean) | 将来の統合先。C-1 初期実装では肥大化させない |

---

## 2. スコープ

### 2.1 含めるもの

| 対象 | 内容 |
|---|---|
| 装置グラフ | 加工装置ノードと Belt / Pipe エッジからなる DAG |
| ストリーム種別 | Shape を運ぶ Belt と、Fluid を運ぶ Pipe の区別 |
| ポート | ノードごとの入力 / 出力 port と、受け付ける stream kind |
| 接続妥当性 | port kind 一致、入力数充足、DAG 性、出力の接続先制約 |
| 評価関数 | 入力ストリームと装置グラフから、観測範囲内の出力ストリームを得る関数 |
| 処理能力 | 抽象的な throughput / capacity / demand / capability |
| 最低装置数 | 目標需要に対する装置数の下界を計算するための抽象枠組み |
| フロー等価性 | 機能的等価性と処理能力等価性の分離 |
| 代表フロー | 切断、回転、積層、着色、混色を含む小規模例 |

### 2.2 含めないもの

| 対象 | 理由 |
|---|---|
| 装置別の具体スループット値 | 調査フェーズで確定するため、この計画では値を断定しない |
| 装置別の具体容量値 | 同上 |
| 装置の占有面積や配置最適化 | C-1 では拡張点のみ。空間制約の最適化は別フェーズに分ける |
| ワイヤー制御の詳細 | C-2 / Layer D で扱う |
| MAM 完全性本体 | Layer D の証明対象として扱う |
| 実ゲーム実測値の表 | 後続調査で作成し、この計画から参照する |

---

## 3. 用語

| 用語 | 意味 | 備考 |
|---|---|---|
| tick | フロー評価で用いる離散時間単位 | Wave Gravity の tick と整合させるが、装置別処理時間の値は未確定 |
| Belt | Shape アイテムを運ぶストリーム | Shape Processing の主経路 |
| Pipe | Fluid を運ぶストリーム | Painter / CrystalGenerator / ColorMixer の入力に必要 |
| Lane | 並列に流れる経路を区別する抽象単位 | 初期実装では同期制約の抽象化に留める |
| Stream | tick に沿って観測される値の列 | finite observation window で扱う |
| StreamKind | Belt / Pipe の種別 | Lean では接続妥当性のキーにする |
| Fluid | Color と抽象量を持つ資源 | 単位や具体量は後続調査まで未確定 |
| MachineNode | 加工装置の 1 インスタンス | 同種装置の複製は別 node として表現する |
| Port | node の入力 / 出力口 | kind と index を持つ |
| FlowGraph | MachineNode と接続 edge からなる DAG | well-formed predicate で妥当性を持つ |
| Throughput | 単位時間あたりに処理できる抽象量 | 具体数値は持たせない |
| Capacity | 入出力や内部待ちの抽象容量 | 具体数値は持たせない |
| Demand | 欲しい出力量または流量 | 目標 production rate の抽象表現 |
| Capability | node / graph が提供できる処理能力 | throughput / capacity / 消費量制約をまとめる |
| Bottleneck | demand に対して最も厳しい capability 制約 | 最低装置数の下界計算に使う |
| Minimum machine count | demand を満たすために必要な装置数の下界 | 空間配置の最適化とは分ける |

---

## 4. モデル設計

### 4.1 StreamKind

Lean 実装では、まず Belt と Pipe を同じ graph 上の異なる stream kind として扱う。

```lean
inductive StreamKind where
  | belt
  | pipe
```

`belt` は `Shape` を運ぶ。`pipe` は `Fluid` を運ぶ。`Fluid` は初期段階では `Color` と抽象量を持つ値として設計し、既存の `Color` / `Color.mix` を再利用する。

```lean
structure Fluid where
  color : Color
  amount : FlowAmount
```

`FlowAmount` は具体的な単位を持たない抽象量として開始する。後続調査で単位や離散化方針が決まるまでは、装置別の実値を定義しない。

### 4.2 Port

各 node は入力 port と出力 port を持つ。接続 edge は出力 port から入力 port へ向かう。

初期実装では、port の型安全性を完全に dependent type へ押し込まず、構造体と well-formed predicate の組み合わせから始める。

```lean
structure PortSpec where
  kind : StreamKind
  name : String

structure NodeSpec where
  inputs : List PortSpec
  outputs : List PortSpec
```

この方針により、Cutter のような多出力 node、Stacker / Swapper のような複数入力 node、Painter / CrystalGenerator のような Belt + Pipe node を同じ枠で扱える。

### 4.3 FlowGraph

`FlowGraph` は装置インスタンスと接続 edge を持つ DAG として扱う。

```lean
structure FlowGraph where
  nodes : List MachineNode
  edges : List FlowEdge
```

妥当性は `FlowGraph.WellFormed` で定義する。

| 条件 | 内容 |
|---|---|
| node id 一意性 | graph 内で node を一意に参照できる |
| edge 端点の存在 | edge が存在する node / port を参照する |
| kind 一致 | 出力 port と入力 port の `StreamKind` が一致する |
| 入力充足 | 評価対象 node の必須入力が満たされる |
| DAG 性 | tick 評価で閉路による即時依存が発生しない |
| split / merge 規約 | 分岐・合流の意味を明示する |
| lane 同期 | 複数入力装置の対応関係を抽象的に表す |

最初から型だけで DAG 性を保証しようとすると実装負荷が高くなるため、初期段階では predicate 方式を採用する。

---

## 5. MachineSpec

`MachineSpec` は装置の入出力 port、抽象処理能力、既存 Operations との対応をまとめる。

```lean
structure MachineSpec where
  ports : NodeSpec
  capability : Capability
```

既存の加工意味論は [../../S2IL/Operations.lean](../../S2IL/Operations.lean) から参照し、Flow 層では再定義しない。

| 分類 | 代表装置 | 入力 | 出力 | core semantics |
|---|---|---|---|---|
| unary shape | Rotator / Reverse Rotator / 180 Rotator / Half-Destroyer / Pin Pusher | Belt | Belt | `Shape.rotateCW`, `Shape.rotateCCW`, `Shape.rotate180`, `Shape.halfDestroy`, `Shape.pinPush` |
| split shape | Cutter | Belt | Belt x 2 | `Shape.cut` |
| binary shape | Stacker / Swapper | Belt x 2 | Belt または Belt x 2 | `Shape.stack`, `Shape.swap` |
| shape + fluid | Painter / CrystalGenerator | Belt + Pipe | Belt | `Shape.paint`, `Shape.crystallize` |
| fluid + fluid | ColorMixer | Pipe x 2 | Pipe | `Color.mix` / `Operations.mix` |
| sink | Trash | Belt | なし | 出力を破棄する抽象 node |

Painter / CrystalGenerator / ColorMixer は Fluid の量や消費量を必要とするが、その具体式はここでは確定しない。初期実装では抽象的な `requires` / `consumes` / `produces` を `Capability` に持たせ、後続調査でインスタンスを埋める。

---

## 6. Capability と最低装置数

### 6.1 基本方針

`Capability` は、装置または graph が持つ処理能力を値として扱うための構造である。

```lean
structure Capability where
  throughput : Throughput
  inputCapacity : Capacity
  outputCapacity : Capacity
```

`Throughput` / `Capacity` は具体数値を持ちうる型として設計するが、この計画では装置別の値を入れない。

### 6.2 解析対象

最低装置数の計算は、空間配置の最適化ではなく、処理能力の下界として開始する。

| 段階 | 証明対象 |
|---|---|
| 単一 node | 1 台の装置が満たせる demand の上限 |
| 直列 graph | graph 全体の throughput は bottleneck で制限される |
| 並列複製 | 同種 node の複製により capability が加算される条件 |
| 複数入力 node | 各入力 stream の demand を同時に満たす条件 |
| fluid 消費 node | Fluid supply が Shape throughput を制限する条件 |

### 6.3 下界計算の形

将来的には、目標 demand と 1 台あたり capability から最低装置数の下界を導く。

```lean
constant minMachineLowerBound : Demand → Capability → Nat
```

この段階では実装本体を置かず、Lean 実装時は theorem 化できる抽象 rate の代数を先に決める。

---

## 7. 評価関数

### 7.1 推奨モデル

評価関数は、tick-indexed stream と finite observation window を基本にする。

```lean
def evaluate (graph : FlowGraph) (window : Nat) (inputs : FlowInputs) : Option FlowOutputs :=
  -- graph の WellFormed 性、入力充足、資源充足を確認して評価する
  none
```

`Option` は最初の候補であり、エラー理由を証明やテストで使いたくなった段階で `Except FlowEvalError` 相当へ拡張する。

### 7.2 評価不能の例

| 状態 | 扱い |
|---|---|
| port kind 不一致 | `WellFormed` で排除 |
| 必須入力不足 | 評価不能 |
| Fluid 不足 | 評価不能または生産停止 |
| DAG でない | `WellFormed` で排除 |
| window 外の出力 | 観測しない |

### 7.3 既存 Operations との接続

Shape 加工の本体は既存関数へ委譲する。

| Flow node | 委譲先 |
|---|---|
| Rotator | `Shape.rotateCW` |
| Reverse Rotator | `Shape.rotateCCW` |
| 180 Rotator | `Shape.rotate180` |
| Half-Destroyer | `Shape.halfDestroy` |
| Cutter | `Shape.cut` |
| Stacker | `Shape.stack` |
| Swapper | `Shape.swap` |
| Painter | `Shape.paint` |
| CrystalGenerator | `Shape.crystallize` |
| ColorMixer | `Color.mix` / `Operations.mix` |

---

## 8. フロー等価性と証明方針

Flow 等価性は 2 種類に分ける。

| 等価性 | 意味 |
|---|---|
| 機能的等価性 | 同じ入力ストリームと観測 window に対して同じ出力を返す |
| 処理能力等価性 | 同じ demand に対して同じ capability bound を持つ |

等変性は Layer A/B と同じ規約を使う。

- CW 回転等変性を主証明にする
- 180° / CCW は CW 版から機械導出する
- E/W 参照操作は [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) の例外規約に従う
- Fluid の `Color` は回転で変化しないものとして扱う

代表的な theorem 目標は次の形になる。

```lean
theorem FlowGraph.evaluate_rotateCW_comm
    (graph : FlowGraph) (window : Nat) (inputs : FlowInputs) :
    -- 入力 Shape stream を CW 回転してから評価しても、出力 Shape stream を CW 回転したものと一致する
    True := by
  trivial
```

上記は形の例であり、実際の命題は `FlowInputs` / `FlowOutputs` の設計後に確定する。

---

## 9. 推奨 Lean ディレクトリ構造

初期実装では、Layer A/B の facade 中心原則を継承する。

```text
S2IL/
├── Flow.lean
└── Flow/
    ├── Types.lean
    ├── Capability.lean
    ├── MachineSpec.lean
    ├── Graph.lean
    ├── Eval.lean
    ├── Equivariance.lean
    └── Internal/
        ├── GraphAcyclic.lean
        ├── PortLookup.lean
        └── CapabilityAlgebra.lean
```

| ファイル | 責務 |
|---|---|
| `S2IL/Flow.lean` | 公開 API の facade。150 行以内を維持する |
| `Flow/Types.lean` | `StreamKind`, `Fluid`, `PortSpec`, id 型などの基礎型 |
| `Flow/Capability.lean` | `Throughput`, `Capacity`, `Demand`, `Capability` |
| `Flow/MachineSpec.lean` | 装置種別、port spec、既存 Operations との対応 |
| `Flow/Graph.lean` | `FlowGraph`, `FlowEdge`, `WellFormed` |
| `Flow/Eval.lean` | tick-indexed stream 評価関数 |
| `Flow/Equivariance.lean` | Flow 評価の回転等変性 |
| `Flow/Internal/*` | graph lookup、DAG、capability 補助補題 |

`S2IL.lean` への `import S2IL.Flow` 追加は、`S2IL/Flow.lean` が成立してから行う。

---

## 10. テスト計画

後続実装では `Test/Flow/` を新設する。

```text
Test/
└── Flow/
    ├── Types.lean
    ├── MachineSpec.lean
    ├── Graph.lean
    ├── Eval.lean
    └── Examples.lean
```

| テスト | 目的 |
|---|---|
| port kind mismatch | `WellFormed` が不正接続を拒否すること |
| cut -> rotate -> cut | 代表フローを graph として表現できること |
| Stacker graph | 複数入力 node を扱えること |
| Painter graph | Belt + Pipe 入力を扱えること |
| ColorMixer graph | Pipe + Pipe 入力を扱えること |
| bottleneck lower bound | 抽象 capability から下界計算の形を検証すること |
| rotateCW equivalence | Flow 評価の等変性 theorem の型を確認すること |

`Test.lean` には `Test.Flow.*` が実体化した段階で import を追加する。

---

## 11. 実装フェーズ

### Phase C1-0: ドキュメント正本の設置

- 本計画書を `docs/plans/` に置く
- [README.md](README.md) から辿れるようにする
- [MILESTONES.md](MILESTONES.md) の C-1 に本計画を正本としてリンクする

### Phase C1-1: Flow 基礎型

- `S2IL/Flow.lean` facade を作る
- `StreamKind`, `Fluid`, `PortSpec`, `NodeId`, `PortId` を定義する
- public 定義には日本語 docstring を付ける
- REPL `#check` で主要型を確認する

### Phase C1-2: Capability 抽象

- `Throughput`, `Capacity`, `Demand`, `Capability` を定義する
- 具体値は preset として置かない
- 比較・加算・下界計算に必要な最小 API を決める

### Phase C1-3: MachineSpec

- Operations facade を import し、装置種別と port spec を対応付ける
- Belt-only、Pipe-only、Belt+Pipe の代表装置を入れる
- `GameConfig` が必要な装置は明示引数として扱う

### Phase C1-4: FlowGraph と WellFormed

- node / edge の構造を定義する
- port lookup と kind 一致を theorem 化する
- DAG 性は predicate として開始する

### Phase C1-5: 評価関数

- finite observation window を持つ tick-indexed evaluation を実装する
- まず小規模 graph の評価を通す
- エラー理由が必要になった段階で `Option` から `Except` 系へ拡張する

### Phase C1-6: 処理能力解析

- 単一 node の capability bound を定義する
- 直列 graph の bottleneck theorem を目標にする
- 並列複製による下界改善を扱う

### Phase C1-7: 等価性と代表フロー

- 機能的等価性と処理能力等価性を定義する
- `cut -> rotate -> cut` などの代表フローを証明対象にする
- CW 等変性を主証明にする

---

## 12. 検証手順

Lean 実装に入った後は、次の順で検証する。

| タイミング | 手順 |
|---|---|
| 新規 API 追加前 | REPL で `#check` 可能な型に落とす |
| `S2IL/Flow.lean` 作成後 | `.github/skills/lean-tooling/scripts/build.ps1 -Target S2IL.Flow` |
| `Test/Flow/*` 追加後 | `.github/skills/lean-tooling/scripts/build.ps1` |
| 大きな proof 追加前 | `lean-theorem-investigator` で counterexample / goal shape を確認する |

ビルドの正本は build script の diagnostics とし、VS Code Problems は判断材料にしない。

---

## 13. 未解決事項

| 項目 | 次アクション |
|---|---|
| Fluid の量単位 | ゲーム仕様調査後に決める |
| 装置別 throughput | 後続調査で正本表を作る |
| 装置別 capacity | 後続調査で正本表を作る |
| 分岐時の stream 複製 / 分配 | Belt / Pipe で同じ規則にするかを決める |
| 合流時の順序 | tick と Lane のどちらで順序付けるかを決める |
| Lane 同期 | 複数入力装置の入力対応をどの粒度で型に入れるかを決める |
| 空間制約 | C-1 拡張または別計画に分離する |

---

## 14. 次の実作業チェックリスト

1. `S2IL/Flow.lean` と `S2IL/Flow/Types.lean` の最小 scaffold を作る
2. `StreamKind` / `Fluid` / `PortSpec` を REPL で型確認する
3. `Flow/Capability.lean` で抽象処理能力の型を決める
4. `Flow/MachineSpec.lean` で装置分類を Lean の inductive に落とす
5. `Flow/Graph.lean` で `WellFormed` の最初の条件を実装する
6. `Test/Flow/` に port kind mismatch と代表 node spec のテストを追加する
7. `S2IL.lean` と `Test.lean` の import を更新する
8. build script で `S2IL.Flow`、続いて全体を検証する