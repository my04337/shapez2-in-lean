# Layer C-1: Shape Processing Flow 計画

- 作成日: 2026-05-05
- 最終更新: 2026-05-06
- ステータス: **設計ドラフト / 基本スループット反映済み / Layer C-1 初期実装完了**
- スコープ: ワイヤーなし Shape Processing フロー、ベルト / パイプのストリーム、固定加工ライン、抽象処理能力

---

## 0. 目的

Layer C-1 では、Layer A/B で定義済みの純粋な加工操作を、実際の加工ラインとして接続・評価できる形に持ち上げる。

本層は **ワイヤー制御を使わない固定 Shape Processing Flow** を扱う。Wires / Signal による条件分岐や動的ルーティングは C-2 以降に分離し、C-1 では「与えられた加工工程を、ワイヤーなしでどの程度表現・評価・処理能力解析できるか」を固める。

本計画の中心は次の 5 点である。

| 観点 | 方針 |
|---|---|
| 接続構造 | 線形パイプラインに限定せず、DAG 形式の加工ラインを初期対象に含める |
| ストリーム | ベルト上の Shape とパイプ上の液剤を区別して扱う |
| 処理能力 | スループット / 容量 / 消費量を first-class な抽象概念として導入する |
| 代表工程 | `halfDestroyer -> reverseRotator -> halfDestroyer` のような加工列を FlowGraph として検証する |
| 数値 | 基本スループット値はゲーム仕様側を正本とし、Lean 側では後から差し込める構造として扱う |

具体的な基本スループット値は [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) を正本とする。本計画では、その値を後から差し込める Lean 側の構造と証明ロードマップを定める。容量値や Flow 設定への取り込み方針は、後続の実装フェーズで確定する。

---

## 1. 参照元と正本の分担

本計画は既存資料の重複説明を避け、次のように正本を分担する。

| 情報 | 正本 | Layer C-1 での扱い |
|---|---|---|
| プロジェクト全体の層構造 | [MILESTONES.md](MILESTONES.md) | C-1 の位置付けを継承する |
| Layer A/B のコード構造 | [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) | facade / Internal / MECE / 等変性規約を継承する |
| `GameConfig` | [../s2il/game-config.md](../s2il/game-config.md) | レイヤ上限の設定として維持し、処理能力設定とは混ぜない |
| ゲーム用語・基本スループット値 | [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) | ベルト / パイプ / レーン / Shape Processing の用語と基本速度の値を再利用する |
| MAM の種類と表現能力 | [../shapez2/mam.md](../shapez2/mam.md) | C-1 は MAM 分類を定義せず、固定加工ラインの表現力として下支えする |
| tick と Wave Gravity | [../shapez2/falling.md](../shapez2/falling.md) | 離散時間モデルの参考にする |
| 加工操作の Lean API | [../../S2IL/Operations.lean](../../S2IL/Operations.lean) | Flow 層から参照する唯一の Operations facade とする |
| Machine 統合層 | [../../S2IL/Machine.lean](../../S2IL/Machine.lean) | 将来の統合先。C-1 初期実装では肥大化させない |

---

## 2. スコープ

### 2.1 含めるもの

| 対象 | 内容 |
|---|---|
| 加工ライン | ワイヤー制御を含まない、マシンとベルト / パイプ接続からなる DAG |
| ストリーム種別 | Shape を運ぶベルトと、液剤を運ぶパイプの区別 |
| ポート | マシンごとの入力 / 出力ポートと、受け付けるストリーム種別 |
| 接続妥当性 | ポートのストリーム種別一致、入力数充足、DAG 性、出力の接続先制約 |
| 評価関数 | 入力ストリームと加工ラインから、観測範囲内の出力ストリームを得る関数 |
| 処理能力 | 抽象的なスループット / 容量 / スループット要求 / 処理能力 |
| 必要マシン数 | スループット要求に対する必要マシン数の下界を計算するための抽象枠組み |
| フロー等価性 | 機能的等価性と処理能力等価性の分離 |
| 代表フロー | 切断処理、回転、積層、着色、混色を含む小規模例 |

### 2.2 含めないもの

| 対象 | 理由 |
|---|---|
| マシン別の具体容量値 | 後続調査で確定するため、この計画では値を断定しない |
| Lean 実装への具体スループット値の直書き | 正本はゲーム仕様側に置き、Flow 側では設定値として取り込める形にする |
| マシンの占有面積や配置最適化 | C-1 では拡張点のみ。空間制約の最適化は別フェーズに分ける |
| ワイヤー制御の詳細 | C-2 / Layer D で扱う。C-1 の評価対象は固定加工ラインに限定する |
| MAM 完全性本体 | Layer D の証明対象として扱う |
| 実ゲーム実測値の正本維持 | 正本は [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) に置き、この計画から参照する |

---

## 3. 用語

| 用語 | 意味 | 備考 |
|---|---|---|
| ティック (tick) | フロー評価で用いる離散時間単位 | Wave Gravity の tick と整合させるが、マシン別処理時間の値は未確定 |
| ベルト (Belt) | Shape アイテムを運ぶ搬送路 | Shape Processing の主経路。C-1 では通常のベルトを扱う |
| パイプ (Pipe) | 液剤を運ぶ搬送路 | Painter / CrystalGenerator / ColorMixer の入力に必要 |
| レーン (Lane) | C-1 では通常ベルト 1 本ぶんの搬送路 | 宇宙ベルトの 12 レーンや、抽象的な stream index とは区別する |
| ストリーム (Stream) | ティックに沿ってベルト / パイプ上で観測される値の流れ | finite observation window で扱う |
| ストリーム種別 (StreamKind) | ベルト / パイプの種別 | Lean では接続妥当性のキーにする |
| 液剤 (Fluid) | Color と抽象量を持つ資源 | スループット単位は L/分。Lean 内部の量表現は後続実装で決める |
| マシン (Machine) | ゲーム内のマシン 1 台 | Lean の graph 表現では `MachineNode` として扱う |
| ポート (Port) | マシンの入力 / 出力接続口 | ゲーム内に明確な名称がないため、設計用語として採用する |
| 加工ライン (FlowGraph) | マシンと接続からなる DAG | Lean の内部名は `FlowGraph`。well-formed predicate で妥当性を持つ |
| スループット (Throughput) | 単位時間あたりに処理できる抽象量 | 基本値はゲーム仕様側を正本とし、Lean では設定値として扱う |
| 容量 (Capacity) | 入出力や内部待ちの抽象容量 | 具体値は後続調査まで未確定 |
| 目標シェイプ (Target Shape) | 作りたい、または納品したい Shape | Shapez2 の納品には現状スループット条件を含めない |
| スループット要求 (Throughput Requirement) | 指定レーン数を満たすなど、加工ラインが満たすべき生産量条件 | 目標シェイプとは別概念として扱う |
| 処理能力 (Capability) | マシン / 加工ラインが提供できる処理能力 | スループット / 容量 / 消費量制約をまとめる |
| ボトルネック (Bottleneck) | スループット要求に対して最も厳しい処理能力制約 | 必要マシン数の下界計算に使う |
| 必要マシン数 (Minimum Machine Count) | スループット要求を満たすために必要なマシン数の下界 | 空間配置の最適化とは分ける |
| 固定加工ライン (Fixed Flow) | ワイヤーや信号による分岐を使わず、あらかじめ決めたマシン列・DAG だけで加工するライン | C-1 の中心対象 |

---

## 4. モデル設計

### 4.1 ストリーム種別 (StreamKind)

Lean 実装では、まずベルトとパイプを同じ加工ライン上の異なるストリーム種別として扱う。

```lean
inductive StreamKind where
  | belt
  | pipe
```

`belt` は `Shape` を運ぶベルトを表す。`pipe` は `Fluid`（液剤）を運ぶパイプを表す。`Fluid` は初期段階では `Color` と抽象量を持つ値として設計し、既存の `Color` / `Color.mix` を再利用する。

```lean
structure Fluid where
  color : Color
  amount : FlowAmount
```

`FlowAmount` は Lean 内部では抽象量として開始する。スループット表では液剤を L/分で扱うが、tick 評価上の離散化方針は後続実装で決める。

### 4.2 ポート (Port)

各マシンは入力ポートと出力ポートを持つ。加工ライン上の接続は、出力ポートから入力ポートへ向かう。

初期実装では、ポートの型安全性を完全に dependent type へ押し込まず、構造体と well-formed predicate の組み合わせから始める。

```lean
structure PortSpec where
  kind : StreamKind
  name : String

structure NodeSpec where
  inputs : List PortSpec
  outputs : List PortSpec
```

この方針により、Cutter のような多出力マシン、Stacker / Swapper のような複数入力マシン、Painter / CrystalGenerator のようなベルト + パイプ入力マシンを同じ枠で扱える。

### 4.3 加工ライン (FlowGraph)

`FlowGraph` はマシンと接続を持つ DAG として扱う。

```lean
structure FlowGraph where
  nodes : List MachineNode
  edges : List FlowEdge
```

妥当性は `FlowGraph.WellFormed` で定義する。

| 条件 | 内容 |
|---|---|
| マシン id 一意性 | 加工ライン内でマシンを一意に参照できる |
| 接続端点の存在 | 接続が存在するマシン / ポートを参照する |
| ストリーム種別一致 | 出力ポートと入力ポートの `StreamKind` が一致する |
| 入力充足 | 評価対象マシンの必須入力が満たされる |
| DAG 性 | tick 評価で閉路による即時依存が発生しない |
| split / merge 規約 | 分岐・合流の意味を明示する |
| レーン同期 | 複数入力マシンの入力対応を表す |

最初から型だけで DAG 性を保証しようとすると実装負荷が高くなるため、初期段階では predicate 方式を採用する。

---

## 5. マシン仕様 (MachineSpec)

`MachineSpec` はマシンの入出力ポート、抽象処理能力、既存 Operations との対応をまとめる。

```lean
structure MachineSpec where
  ports : NodeSpec
  capability : Capability
```

既存の加工意味論は [../../S2IL/Operations.lean](../../S2IL/Operations.lean) から参照し、Flow 層では再定義しない。

| 分類 | 代表マシン | 入力 | 出力 | core semantics |
|---|---|---|---|---|
| 単入力 Shape | Rotator / Reverse Rotator / 180 Rotator / Half-Destroyer / Pin Pusher | ベルト | ベルト | `Shape.rotateCW`, `Shape.rotateCCW`, `Shape.rotate180`, `Shape.halfDestroy`, `Shape.pinPush` |
| 分割 Shape | Cutter | ベルト | ベルト x 2 | `Shape.cut` |
| 2入力 Shape | Stacker / Swapper | ベルト x 2 | ベルト または ベルト x 2 | `Shape.stack`, `Shape.swap` |
| Shape + 液剤 | Painter / CrystalGenerator | ベルト + パイプ | ベルト | `Shape.paint`, `Shape.crystallize` |
| 液剤 + 液剤 | ColorMixer | パイプ x 2 | パイプ | `Color.mix` / `Operations.mix` |
| 廃棄 | Trash | ベルト | なし | 出力を破棄する抽象マシン |

Painter / CrystalGenerator / ColorMixer は液剤の量や消費量を必要とする。基本速度での液剤量は [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) を正本とし、初期実装では抽象的な `requires` / `consumes` / `produces` を `Capability` に持たせて、後から設定値として差し込める形にする。

---

## 6. 処理能力 (Capability) と必要マシン数

### 6.1 基本方針

`Capability` は、マシンまたは加工ラインが持つ処理能力を値として扱うための構造である。

```lean
structure Capability where
  throughput : Throughput
  inputCapacity : Capacity
  outputCapacity : Capacity
  requires : List Throughput
  consumes : List Throughput
  produces : List Throughput
```

`Throughput` / `Capacity` は具体数値を持ちうる型として設計するが、Flow 層の初期実装では基本スループット値を直接ハードコードしない。正本表の値は、後続の `FlowConfig` / `SpeedTier` 相当の設定から取り込める形にする。

`FlowAmount` は `units : Nat` を持つ抽象量として開始している。台数計算ではまず `units` 上の自然数演算として下界を定義し、`個/分` や `L/分` への解釈は設定層に委ねる。

### 6.2 解析対象

必要マシン数の計算は、空間配置の最適化ではなく、処理能力の下界として開始する。

| 段階 | 証明対象 |
|---|---|
| 単一マシン | 1 台のマシンが満たせるスループット要求の上限 |
| 直列加工ライン | 加工ライン全体のスループットはボトルネックで制限される |
| 並列複製 | 同種マシンの複製により処理能力が加算される条件 |
| 複数入力マシン | 各入力ストリームのスループット要求を同時に満たす条件 |
| 液剤消費マシン | 液剤供給が Shape スループットを制限する条件 |

### 6.3 下界計算の形

将来的には、スループット要求と 1 台あたりの処理能力から必要マシン数の下界を導く。最初の実装対象は、ゼロ除算とストリーム種別不一致を除外できる形の ceiling division とする。

```lean
def ceilDiv (target perMachine : FlowAmount) : Option Nat :=
  -- perMachine.units = 0 の場合は none
  -- それ以外は ⌈target.units / perMachine.units⌉
  none

def minMachineCount (target machine : Throughput) : Option Nat :=
  -- target.kind = machine.kind の場合に ceilDiv target.amount machine.amount
  none
```

この単一ストリームの計算を土台に、次の順で拡張する。

| 段階 | 計算 | 証明義務 |
|---|---|---|
| 単一マシン | `ceilDiv target machine` | 算出台数ぶんの処理能力が要求量以上になる |
| 直列固定ライン | 各段の必要台数を算出し、全段の合計を取る | どの段も要求スループットを下回らない |
| 既存ラインのボトルネック | 各段の実効スループットの最小値を取る | 出力スループットがボトルネックを超えない |
| 同種並列複製 | 台数倍で同種マシンの処理能力を加算する | 加算後 capability が単体 capability の上界を保つ |
| 複数入力マシン | 各入力ストリームの要求を同時に満たす | 入力不足時に評価できないことを示す |
| 液剤消費マシン | `requires` / `consumes` / `produces` を要求に含める | Shape 側と液剤側の両制約を満たす |

配置面積、ベルト合流の具体配線長、宇宙ベルトのレーン割当はこの下界計算には含めない。

### 6.4 基本スループット値の参照

具体的な基本スループット値の正本は [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) とする。本節は C-1 実装で参照する代表値の要約であり、正本表の重複維持を目的としない。

前提:

- 基本速度を基準値とする
- アップグレード倍率は別設定として扱う
- Shape の処理量は `個/分`、液剤の処理量は `L/分` で表す
- 液剤系は、ゲーム内表記に合わせて「液剤ランチャー 1 台がカバーできるマシン数」も併記する

| カテゴリ | 項目 | 基本値 | C-1 での扱い |
|---|---|---|---|
| ベルト搬送 | ベルト / ベルトランチャー / ベルトレシーバー | 120 個/分 | 通常ベルト 1 本分の基準 |
| 宇宙ベルト | 宇宙ベルト | 480 個/分 / レーン、4 レーン / 層。3 層基準で 5,760 個/分 | 2 層 / 3 層は設定で切り替え可能にする |
| パイプ搬送 | パイプ | 同一セグメント内は無限 | セグメントは接続されたパイプ設置物の連結単位。マシン越しは別セグメント |
| パイプ接続 | 液剤ランチャー / 液剤レシーバー | 1,200 L/分 | 液剤供給の接続制約 |
| 宇宙パイプ | 宇宙パイプ | 28,800 L/分 | 宇宙プラットフォーム間の液剤搬送制約 |
| Shape マシン | 回転機 / 逆回転機 / 180度回転機 | 60 個/分 | 2 台でベルト 1 本分 |
| Shape マシン | 切断処理機 / ピン押し機 | 40 個/分 | 3 台でベルト 1 本分 |
| Shape マシン | 切断機 / スワップ機 / 積層機 | 30 個/分 | 4 台で入力ベルト 1 本分 |
| 産出 | ミニ採掘機 | 30 個/分 | 4 台でベルト 1 本分 |
| 液剤供給 | ミニポンプ | 300 L/分 | 4 台 / 液剤ランチャー |
| Shape + 液剤 | 着色機 | 30 個/分、液剤 300 L/分 | 4 台でベルト 1 本分、4 台 / 液剤ランチャー |
| 液剤 + 液剤 | 混色機 | 入力 300 L/分 x 2、出力 600 L/分 | 入力: 4 台 / 液剤ランチャー x 2、出力: 2 台 / 液剤ランチャー |
| Shape + 液剤 | 結晶製造機 | 20 個/分、液剤 400 L/分 | 6 台でベルト 1 本分、3 台 / 液剤ランチャー |

### 6.5 代表台数計算: 象限抽出ライン

通常ベルト 1 本ぶん、すなわち `120 個/分` を既定スループット要求とする。
NE 象限抽出の代表工程は次の固定加工ラインとして扱う。

```text
CuCuCuCu
  -> Half-Destroyer
  -> Reverse Rotator
  -> Half-Destroyer
  -> Cu------
```

基本速度では、切断処理機は `40 個/分`、逆回転機は `60 個/分` である。
したがって通常ベルト 1 本を満たす下界は次の通り。

| 段 | 1 台あたり | 要求 | 必要台数 |
|---|---|---|---|
| Half-Destroyer | 40 個/分 | 120 個/分 | `ceil(120 / 40) = 3` |
| Reverse Rotator | 60 個/分 | 120 個/分 | `ceil(120 / 60) = 2` |
| Half-Destroyer | 40 個/分 | 120 個/分 | `ceil(120 / 40) = 3` |

この固定ラインの下界は合計 8 台である。これはマシン台数の処理能力下界であり、ベルト、ランチャー、配置面積、ワイヤー制御は含めない。

### 6.6 代表台数計算: 4 レイヤ end-to-end ライン

より複雑な end-to-end 代表例として、次の 4 レイヤシェイプを通常ベルト 1 本ぶん出力する固定加工ラインを扱う。

```text
Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu
```

ここでは Shape Code の左から右を下層から上層への積層順として読む。必要な外部入力ストリームは次の通り。

| 入力 | 用途 | 要求 |
|---|---|---|
| `RuRuRuRu` | 1 本は `RbRbRbRb` への着色、1 本は 2 層目として積層 | 2 ベルト |
| `SuSuSuSu` | 最上層として積層 | 1 ベルト |
| color-b 液剤 | `RuRuRuRu` から `RbRbRbRb` への着色 | 1 ベルトぶんの着色量 |

加工工程は次の composite subflow に分けて計画する。

| subflow | 入力 | 出力 | 処理能力上の扱い |
|---|---|---|---|
| Paint-Ru-to-Rb | `RuRuRuRu` 1 ベルト + color-b 液剤 | `RbRbRbRb` 1 ベルト | Painter 4 台、液剤 1200 L/分を要求する |
| Diagonal-Split | `RbRbRbRb` 1/2 ベルト | `Rb--Rb--` 1 ベルト | Cutter / Rotator / Swapper / Rotator の固定 DAG として扱う |
| Diagonal-Split x2 | `RbRbRbRb` 1 ベルト | `Rb--Rb--` 2 ベルト | Diagonal-Split を 2 セット並列に置く |
| Stack-4Layers | `Rb--Rb--` 2 ベルト + `RuRuRuRu` 1 ベルト + `SuSuSuSu` 1 ベルト | 目標シェイプ 1 ベルト | 3 段の Stacker 列として扱う |

Diagonal-Split は、ne/sw のみを残すための固定 DAG として次のように分解する。

```text
input:
  RbRbRbRb @ 60 個/分

split:
  Cutter x2
    each: RbRbRbRb -> (RbRb----, ----RbRb)
    merge first outputs  -> RbRb---- @ 60 個/分
    merge second outputs -> ----RbRb @ 60 個/分

rotate halves:
  Rotator x1: RbRb---- -> --RbRb--
  Rotator x1: ----RbRb -> Rb----Rb

swap:
  Swapper x2
    each: --RbRb-- + Rb----Rb -> (Rb--Rb--, --Rb--Rb)
    merge first outputs  -> Rb--Rb-- @ 60 個/分
    merge second outputs -> --Rb--Rb @ 60 個/分

rotate second diagonal:
  Rotator x1: --Rb--Rb -> Rb--Rb--

merge:
  Rb--Rb-- @ 60 個/分 + Rb--Rb-- @ 60 個/分 -> Rb--Rb-- @ 120 個/分
```

この subflow は切断分離機（Cutter）が 2 台しかないため、入力は `60 個/分`、つまり通常ベルト 1/2 本ぶんまでしか処理できない。一方で、2 つの Swapper 出力を片方だけ追加回転してマージすることで、`Rb--Rb--` を通常ベルト 1 本ぶん出力できる。

Diagonal-Split 1 セットの台数下界は次の通り。

| 段 | 1 台あたり | 要求 | 必要台数 |
|---|---|---|---|
| Cutter | 30 個/分 | 60 個/分 | `ceil(60 / 30) = 2` |
| Rotator for split halves | 60 個/分 | 60 個/分 x 2 系統 | 2 |
| Swapper | 30 個/分 | 60 個/分 | `ceil(60 / 30) = 2` |
| Rotator for second diagonal | 60 個/分 | 60 個/分 | `ceil(60 / 60) = 1` |

したがって Diagonal-Split 1 セットは 7 台、2 セットでは 14 台を下界とする。

Stack-4Layers は下から順に積む。

```text
stack1: Rb--Rb-- + RuRuRuRu -> Rb--Rb--:RuRuRuRu
stack2: stack1   + Rb--Rb-- -> Rb--Rb--:RuRuRuRu:Rb--Rb--
stack3: stack2   + SuSuSuSu -> Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu
```

既知の単体速度だけで確定できる下界は次の通り。

| 段 | 1 台あたり | 要求 | 必要台数 |
|---|---|---|---|
| Painter | 30 個/分 | 120 個/分 | `ceil(120 / 30) = 4` |
| Diagonal-Split x2 | 7 台 / set | 2 set | 14 |
| Stacker stage 1 | 30 個/分 | 120 個/分 | `ceil(120 / 30) = 4` |
| Stacker stage 2 | 30 個/分 | 120 個/分 | `ceil(120 / 30) = 4` |
| Stacker stage 3 | 30 個/分 | 120 個/分 | `ceil(120 / 30) = 4` |

このため、外部入力の採掘機、液剤生成、液剤ランチャー、ベルト、配置面積、ワイヤー制御を除く代表ライン全体では 30 台が下界になる。

---

## 7. 評価関数

### 7.1 推奨モデル

評価関数は、tick-indexed stream と finite observation window を基本にする。

```lean
def evaluate (graph : FlowGraph) (window : Nat) (inputs : FlowInputs) : Option FlowOutputs :=
  -- 加工ラインの WellFormed 性、入力充足、資源充足を確認して評価する
  none
```

`Option` は最初の候補であり、エラー理由を証明やテストで使いたくなった段階で `Except FlowEvalError` 相当へ拡張する。

### 7.2 評価不能の例

| 状態 | 扱い |
|---|---|
| ポートのストリーム種別不一致 | `WellFormed` で排除 |
| 必須入力不足 | 評価不能 |
| 液剤不足 | 評価不能または生産停止 |
| DAG でない | `WellFormed` で排除 |
| window 外の出力 | 観測しない |

### 7.3 既存 Operations との接続

Shape 加工の本体は既存関数へ委譲する。

| Flow マシン | 委譲先 |
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

### 7.4 代表固定フロー: 象限抽出

最初の end-to-end 代表例は、MAM のシミュレーション処理と同じ形を実機処理の固定加工ラインとして表す。

```text
input:  CuCuCuCu
flow:   halfDestroyer -> reverseRotator -> halfDestroyer
output: Cu------
```

実装順序は次の通り。

1. Operations 直呼びで `Shape.halfDestroy (Shape.rotateCCW (Shape.halfDestroy input)) = expected` を検証する
2. 同じ工程を `FlowGraph` と `MachineKind.semantics` で表す
3. `FlowGraph.WellFormed` を確認する
4. `Flow/Eval.lean` の評価関数で同じ出力を得る
5. §6.5 の必要台数計算と同じ `ThroughputRequirement` を使って下界を検証する

### 7.5 代表固定フロー: 4 レイヤ end-to-end

より実用的な代表例として、着色、斜め抽出、並列 subflow、3 段積層を含む固定加工ラインを扱う。

```text
inputs:
  RuRuRuRu @ 2 belts
  SuSuSuSu @ 1 belt
  color-b fluid for 1 belt of painting

paint:
  RuRuRuRu -> RbRbRbRb

diagonal split:
  RbRbRbRb @ 1 belt
    -> Diagonal-Split A @ 1/2 belt -> Rb--Rb-- @ 1 belt
    -> Diagonal-Split B @ 1/2 belt -> Rb--Rb-- @ 1 belt

stack:
  Rb--Rb--
  RuRuRuRu
  Rb--Rb--
  SuSuSuSu

output:
  Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu
```

この例は C-1 の評価関数に対して、次の能力を要求する。

| 要求 | 確認したいこと |
|---|---|
| 複数外部入力 | `RuRuRuRu` 2 ベルトと `SuSuSuSu` 1 ベルトを別ストリームとして受け取れる |
| ベルト + パイプ入力 | Painter が Shape と color-b 液剤を同時に消費できる |
| subflow の内部展開 | Diagonal-Split を Cutter / Rotator / Swapper / Rotator の固定 DAG として表せる |
| subflow の並列複製 | Diagonal-Split を 2 セット置き、`Rb--Rb--` を 2 ベルト出力できる |
| 複数段 Stacker | 下から順に 4 レイヤへ積み上げる評価を記述できる |
| 処理能力解析 | Painter / Diagonal-Split / Stacker の各段が通常ベルト 1 本要求を満たすか確認できる |

実装順序は次の通り。

1. Operations 直呼びで `Shape.stack` を 3 回合成し、目標 Shape Code が得られることを検証する
2. `Diagonal-Split` の内部を Cutter / Rotator / Swapper / Rotator の graph として表す
3. `Diagonal-Split` を 2 セット並列に置いた end-to-end graph を表す
4. `FlowGraph.WellFormed` と stream kind 一致を確認する
5. `Flow/Eval.lean` の評価関数で同じ出力を得る
6. §6.6 の throughput requirement を使い、既知段階と Diagonal-Split 展開後の必要台数下界を検証する

---

## 8. フロー等価性と証明方針

Flow 等価性は 2 種類に分ける。

| 等価性 | 意味 |
|---|---|
| 機能的等価性 | 同じ入力ストリームと観測 window に対して同じ出力を返す |
| 処理能力等価性 | 同じスループット要求に対して同じ capability bound を持つ |

等変性は Layer A/B と同じ規約を使う。

- CW 回転等変性を主証明にする
- 180° / CCW は CW 版から機械導出する
- E/W 参照操作は [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) の例外規約に従う
- 液剤の `Color` は回転で変化しないものとして扱う

代表的な theorem 目標は次の形になる。

```lean
theorem FlowGraph.evaluate_rotateCW_comm
    (graph : FlowGraph) (window : Nat) (inputs : FlowInputs) :
    -- 入力 Shape ストリームを CW 回転してから評価しても、出力 Shape ストリームを CW 回転したものと一致する
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
    ├── Examples.lean
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
| `Flow/Capability.lean` | `Throughput`, `Capacity`, `ThroughputRequirement`, `Capability` |
| `Flow/MachineSpec.lean` | マシン種別、port spec、既存 Operations との対応 |
| `Flow/Graph.lean` | `FlowGraph`, `FlowEdge`, `WellFormed` |
| `Flow/Eval.lean` | tick-indexed stream 評価関数 |
| `Flow/Examples.lean` | 代表固定フローの graph 定義と実装例 |
| `Flow/Equivariance.lean` | Flow 評価の回転等変性 |
| `Flow/Internal/*` | graph lookup、DAG、capability 補助補題 |

`S2IL.lean` への `import S2IL.Flow` は追加済みである。今後 `Flow/Eval.lean` などの新規公開サブモジュールを追加した場合は、`S2IL/Flow.lean` facade 経由で段階的に公開する。

---

## 10. テスト計画

後続実装では既存の `Test/Flow/` を拡張する。

```text
Test/
└── Flow/
    ├── Types.lean
    ├── Capability.lean
    ├── MachineSpec.lean
    ├── Graph.lean
    ├── Eval.lean
    └── Examples.lean
```

| テスト | 目的 |
|---|---|
| ポート種別不一致 | `WellFormed` が不正接続を拒否すること |
| capability lower bound | `ceil(120 / 40) = 3`、`ceil(120 / 60) = 2` を検証すること |
| halfDestroy -> reverseRotator -> halfDestroy | 代表フローを加工ラインとして表現できること |
| Diagonal-Split internal graph | Cutter / Rotator / Swapper / Rotator で `RbRbRbRb` 1/2 ベルトから `Rb--Rb--` 1 ベルトを得ること |
| Rb/Ru/Su 4-layer end-to-end | 着色、Diagonal-Split x2、3 段 Stacker を含む代表フローを表現できること |
| Stacker 加工ライン | 複数入力マシンを扱えること |
| Painter 加工ライン | ベルト + パイプ入力を扱えること |
| ColorMixer 加工ライン | パイプ + パイプ入力を扱えること |
| bottleneck lower bound | 抽象処理能力から下界計算の形を検証すること |
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

- `Throughput`, `Capacity`, `ThroughputRequirement`, `Capability` を定義する
- 基本スループット値は直接 preset として置かず、後続の設定値として取り込める構造にする
- 比較・加算・下界計算に必要な最小 API を決める

### Phase C1-3: MachineSpec

- Operations facade を import し、マシン種別と port spec を対応付ける
- ベルトのみ、パイプのみ、ベルト + パイプの代表マシンを入れる
- `GameConfig` が必要なマシンは明示引数として扱う

### Phase C1-4: FlowGraph と WellFormed

- マシン / 接続の構造を定義する
- port lookup と kind 一致を theorem 化する
- DAG 性は predicate として開始する

### Phase C1-5: 評価関数

- finite observation window を持つ tick-indexed evaluation を実装する
- まず小規模加工ラインの評価を通す
- エラー理由が必要になった段階で `Option` から `Except` 系へ拡張する

### Phase C1-6: 処理能力解析

- `Flow/Internal/CapabilityAlgebra.lean` で `ceilDiv` と単一マシンの capability bound を定義する
- 直列加工ラインの bottleneck theorem を目標にする
- 並列複製による下界改善を扱う
  - 代表値として `120 / 40 -> 3`、`120 / 60 -> 2` を `Test/Flow/Capability.lean` で検証する

### Phase C1-7: 等価性と代表フロー

- 機能的等価性と処理能力等価性を定義する
- `halfDestroyer -> reverseRotator -> halfDestroyer` などの代表フローを証明対象にする
- `Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu` の end-to-end 代表フローを、Diagonal-Split の内部 graph まで含めて段階的に展開する
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
| 液剤の量単位 | スループット単位は L/分で扱う。Lean 内部の `FlowAmount` 離散化方針を決める |
| マシン別スループット | [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) の基本スループット表を正本とし、Flow 設定への取り込み方針を決める |
| マシン別容量 | 後続調査で正本表を作る |
| 速度設定 | 基本速度、アップグレード倍率、宇宙ベルトの 2 層 / 3 層差を `GameConfig` とは別に表すかを決める |
| 分岐時のストリーム複製 / 分配 | ベルト / パイプで同じ規則にするかを決める |
| 合流時の順序 | ティックとレーンのどちらで順序付けるかを決める |
| レーン同期 | 複数入力マシンの入力対応をどの粒度で型に入れるかを決める |
| 空間制約 | C-1 拡張または別計画に分離する |

---

## 14. TODO リスト

本節は、Layer C-1 の完了済み項目と次に着手する作業を 1 箇所で追跡する TODO リストである。完了した行は `完了` にし、成果物 / 完了条件へ検証コマンドや参照先を追記する。

| ID | 状態 | 種別 | TODO | 成果物 / 完了条件 |
|---|---|---|---|---|
| C1-DOC-1 | 完了 | docs | 初期設計計画を作成する | 本計画書を作成し、C-1 の目的・スコープ・実装フェーズを整理済み |
| C1-DOC-2 | 完了 | docs | 用語をゲーム寄せに整理する | ベルト / パイプ / 液剤 / マシン / 加工ライン / 必要マシン数へ表記を整理済み |
| C1-DOC-3 | 完了 | docs | 基本スループット正本を整備する | [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) に基本速度の正本表を追加済み |
| C1-DOC-4 | 完了 | docs | 液剤ランチャー換算を併記する | 着色機・混色機・ミニポンプ・結晶製造機の台数 / 液剤ランチャーを反映済み |
| C1-DOC-5 | 完了 | docs | Layer C 関連インデックスを同期する | [README.md](README.md) / [MILESTONES.md](MILESTONES.md) の C-1 説明を更新済み |
| C1-PLAN-1 | 完了 | plan | ワイヤーフリー固定加工ラインを明確化する | C-1 を Wires / Signal なしの固定 Shape Processing Flow として位置付け、C-2 / Layer D との境界を明記済み |
| C1-PLAN-2 | 完了 | plan | 象限抽出の代表工程と台数計算を追加する | `halfDestroyer -> reverseRotator -> halfDestroyer` と通常ベルト 1 本ぶんの下界 8 台を実装目標に追加済み |
| C1-PLAN-3 | 完了 | plan | 4 レイヤ end-to-end 代表例を追加する | `Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu` を、Painter / Diagonal-Split x2 / Stacker x3 の代表固定フローとして追加済み |
| C1-PLAN-4 | 完了 | plan | Diagonal-Split 内部工程を分解する | `RbRbRbRb` 1/2 ベルトから `Rb--Rb--` 1 ベルトを得る Cutter / Rotator / Swapper / Rotator graph と 7 台下界を追加済み |
| C1-IMPL-1 | 完了 | impl | `S2IL/Flow` scaffold を追加する | `S2IL/Flow.lean` と `S2IL/Flow/Types.lean` を追加し、`S2IL.lean` から公開済み |
| C1-IMPL-2 | 完了 | impl | ストリーム / 液剤 / ポート基礎型を実装する | `StreamKind` / `FlowAmount` / `Fluid` / `PortSpec` / `NodeId` / `PortId` を実装し、REPL `#check` と build script で検証済み |
| C1-IMPL-3 | 完了 | impl | 抽象処理能力を実装する | `S2IL/Flow/Capability.lean` を追加し、`Throughput` / `Capacity` / `ThroughputRequirement` / `Capability` を REPL `#check` と build script で検証済み |
| C1-IMPL-4 | 完了 | impl | マシン仕様を実装する | `S2IL/Flow/MachineSpec.lean` を追加し、Operations facade と対応する `MachineKind` / `MachineSpec` を実装・代表テスト済み |
| C1-IMPL-5 | 完了 | impl | 加工ライン妥当性を実装する | `S2IL/Flow/Graph.lean` と `Test/Flow/Graph.lean` を追加し、端点存在・種別一致・NodeId 順 DAG 近似の `FlowGraph.WellFormed` を代表テスト済み |
| C1-NEXT-1 | 未着手 | impl | `ceilDiv` と単一マシン必要台数を定義する | `Flow/Internal/CapabilityAlgebra.lean` を追加する |
| C1-NEXT-2 | 未着手 | test | 基本下界計算を検証する | `Test/Flow/Capability.lean` で `ceil(120 / 40) = 3`、`ceil(120 / 60) = 2` を検証する |
| C1-NEXT-3 | 未着手 | impl | finite observation window の評価関数を設計する | `Flow/Eval.lean` を追加し、入力ストリームから出力ストリームを得る形を確定する |
| C1-NEXT-4 | 未着手 | example | 象限抽出代表フローを検証する | `Flow/Examples.lean` / `Test/Flow/Examples.lean` で `halfDestroyer -> reverseRotator -> halfDestroyer` を検証する |
| C1-NEXT-5 | 未着手 | example | Diagonal-Split 内部 graph を検証する | `Flow/Examples.lean` / `Test/Flow/Examples.lean` で `RbRbRbRb` 1/2 ベルトから `Rb--Rb--` 1 ベルトを得る |
| C1-NEXT-6 | 未着手 | example | 4 レイヤ end-to-end graph を検証する | `Flow/Examples.lean` / `Test/Flow/Examples.lean` で `Rb--Rb--:RuRuRuRu:Rb--Rb--:SuSuSuSu` の decomposed graph を検証する |
| C1-NEXT-7 | 未着手 | proof | port lookup 補題を分離する | 必要に応じて `Flow/Internal/PortLookup.lean` を追加する |
| C1-NEXT-8 | 未着手 | proof | DAG 判定を一般化する | `Flow/Internal/GraphAcyclic.lean` で NodeId 順 DAG 近似を一般の DAG 判定へ拡張する |
| C1-NEXT-9 | 未着手 | proof | 機能的等価性と回転等変性の型を確定する | `Flow/Equivariance.lean` を追加する |
| C1-NEXT-10 | 未着手 | config | 具体スループット値の設定層を設計する | `FlowConfig` / `SpeedTier` 相当を別フェーズで設計する |
