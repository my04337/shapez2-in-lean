# Layer C-1: Shape Processing Flow 計画

- 作成日: 2026-05-05
- 最終更新: 2026-05-06
- ステータス: **未解決事項整理フェーズ / 初期実装完了済み**
- スコープ: ワイヤーなし Shape Processing フロー、ベルト / パイプのストリーム、固定加工ライン、抽象処理能力

---

## 0. この資料の役割

Layer C-1 は、Layer A/B で定義した純粋な Shape 加工操作を、ワイヤー制御を使わない固定加工ラインとして接続・評価・処理能力解析できる形に持ち上げる層である。

初期実装は一通り完了したため、この資料は詳細な実装手順書ではなく、次の判断を進めるための計画書として維持する。

| 目的 | 内容 |
|---|---|
| 現在地の共有 | C-1 で既に実装済みの範囲を短く確認する |
| 正本の整理 | 詳細仕様・実装・テストの参照先を明確にする |
| 未解決事項の判断 | 仕様上まだ決めるべき項目について、問題概要と対処案を並べる |
| 次アクション選定 | 今後どの設計判断から着手するかを決める材料にする |

---

## 1. 現在地

C-1 の初期実装では、Flow の基礎型、処理能力抽象、マシン仕様、FlowGraph、有限観測 window の評価 API、代表 graph、回転等変性の型、基本スループット設定層までを実装済みである。

今後の中心は、実装済みの骨格に対して **ゲーム仕様に近いストリーム意味論をどこまで入れるか** を決めることに移る。特に、分岐・合流・複数入力同期・液剤量・速度設定・容量・空間制約は、単独の API 追加ではなく Flow 評価の意味を左右する。

---

## 2. 参照元と正本

この資料では既存情報を重複維持しない。詳細は次の正本を参照する。

| 情報 | 正本 |
|---|---|
| プロジェクト全体の層構造 | [MILESTONES.md](MILESTONES.md) |
| Layer A/B の設計原則 | [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) |
| C-1 の公開 API | [../../S2IL/Flow.lean](../../S2IL/Flow.lean) |
| Flow の実装 | [../../S2IL/Flow/](../../S2IL/Flow/) |
| Flow の代表テスト | [../../Test/Flow/](../../Test/Flow/) |
| Shapez2 用語・基本スループット値 | [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) |
| tick と Wave Gravity | [../shapez2/falling.md](../shapez2/falling.md) |
| MAM の種類と表現能力 | [../shapez2/mam.md](../shapez2/mam.md) |
| Lean 実装検証手順 | [../agent/agent-operations-playbook.md](../agent/agent-operations-playbook.md) |

---

## 3. C-1 の固定境界

### 3.1 含めるもの

| 対象 | 扱い |
|---|---|
| 固定加工ライン | ワイヤー制御を含まない MachineNode と接続からなる FlowGraph |
| ストリーム種別 | Shape を運ぶベルトと、液剤を運ぶパイプを区別する |
| ポート | MachineSpec の入力 / 出力ポートで StreamKind を管理する |
| 妥当性 | 端点存在、ポート種別一致、DAG 性を WellFormed で判定する |
| 評価 | finite observation window 上の入力から出力を得る API を持つ |
| 処理能力 | Throughput / Capacity / Capability / minMachineCount を扱う |
| 代表フロー | 象限抽出、Diagonal-Split、4 レイヤ end-to-end を実装例にする |

### 3.2 まだ固定しないもの

| 対象 | 理由 |
|---|---|
| 実ゲームの完全なベルト物理 | C-1 では固定フロー評価の意味を先に固める |
| ワイヤー制御 | C-2 以降に分離する |
| MAM 完全性本体 | Layer D の証明対象にする |
| 配置最適化 | 処理能力下界とは別問題として扱う |
| 実測容量値 | 正本調査が必要なため、抽象容量として保持する |

---

## 4. 実装済み API の要約

詳細な型や theorem は facade を正本とし、この節では位置だけを示す。

| 領域 | 実装 |
|---|---|
| 基礎型 | `StreamKind`, `FlowAmount`, `Fluid`, `PortSpec`, `NodeId`, `PortId` |
| 処理能力 | `Throughput`, `Capacity`, `ThroughputRequirement`, `Capability` |
| 台数下界 | `ceilDiv`, `minMachineCount` |
| マシン仕様 | `MachineKind`, `MachineSpec`, Operations facade への対応 |
| graph | `MachineNode`, `FlowEdge`, `FlowGraph`, `FlowGraph.WellFormed` |
| lookup / DAG | `PortLookup`, `GraphAcyclic` |
| 評価 | `FlowItem`, `FlowStream`, `FlowInputs`, `FlowOutputs`, `FlowGraph.evaluate` |
| 等価性 | `FlowGraph.FunctionallyEquivalent`, 回転等変性の Prop 型 |
| 設定 | `SpeedTier`, `FlowConfig`, `FlowConfig.basic` |
| 代表例 | `diagonalSplitGraph`, `fourLayerEndToEndGraph` |

---

## 5. 代表フローの扱い

代表フローは、C-1 の仕様そのものではなく、評価 API と処理能力 API が最低限表現できることを確認するサンプルである。

| 代表例 | 現状 | 主な検証 |
|---|---|---|
| 象限抽出 | 実装済み | `halfDestroyer -> reverseRotator -> halfDestroyer` の台数下界 8 台 |
| Diagonal-Split | 実装済み | Cutter / Rotator / Swapper / Rotator graph と代表 I/O |
| 4 レイヤ end-to-end | 実装済み | Painter / Diagonal-Split x2 / Stacker x3 の構造的出力と 30 台下界 |

代表例の細かい工程説明は、今後この計画書では増やさない。必要な場合は [../../S2IL/Flow/Examples.lean](../../S2IL/Flow/Examples.lean) と [../../Test/Flow/Examples.lean](../../Test/Flow/Examples.lean) を正本にする。

---

## 6. 処理能力モデルの現在形

C-1 では、必要台数計算を空間配置や配線長の最適化とは分け、処理能力の下界として扱う。

| 概念 | 現在の扱い |
|---|---|
| `FlowAmount` | `units : Nat` を持つ抽象量 |
| `Throughput` | `StreamKind` と量の組 |
| `Capability` | throughput / capacity / requires / consumes / produces をまとめる値 |
| `ceilDiv` | 0 処理量を `none` にする自然数 ceiling division |
| `minMachineCount` | StreamKind 一致時に必要台数下界を返す |

ここでの未解決点は、計算式そのものではなく、`units` をゲーム内の `個/分`・`L/分`・tick 内量・観測 item 量のどれとして解釈するかである。判断カードは §12.2 に置く。

---

## 7. 評価モデルの現在形

評価 API は finite observation window を持つ tick-indexed stream を入口にしている。現時点では、固定 graph の構造と代表出力を扱える最小 API であり、実ゲームの搬送挙動を完全に固定したものではない。

今後決める必要がある意味論は次の 3 つに集約できる。

| 未確定領域 | 影響 |
|---|---|
| 分岐 | 1 つの出力を複数接続したときに複製・分配・禁止のどれにするか |
| 合流 | 複数出力が同じ入力 / ストリームへ入るときの順序をどう決めるか |
| 同期 | Stacker / Swapper など複数入力マシンが入力 item をどう対応付けるか |

この 3 点は互いに独立ではない。先に単純な評価関数だけを拡張すると、後から物理寄りの意味へ戻しにくくなるため、§12.6 から §12.8 をまとめて判断する。

---

## 8. FlowConfig の現在形

基本スループット値はゲーム仕様資料を正本とし、Lean 側では `FlowConfig` から参照する形を取る。

| 項目 | 現状 |
|---|---|
| 基本速度 | `FlowConfig.basic` として実装済み |
| マシン別速度 | `MachineKind` から参照する API の土台あり |
| アップグレード倍率 | まだ意味論を固定していない |
| 宇宙ベルト / 宇宙パイプ | C-1 通常フローとは分けて扱う予定 |
| `GameConfig` との関係 | レイヤ上限設定とは混ぜない方針を維持する |

設定層の次の課題は、「値を置くこと」ではなく、正本表との同期方法、速度 tier の表現、通常ベルト以外の搬送単位をどの段階で取り込むかである。

---

## 9. 証明と等価性の現在形

C-1 では Flow 等価性を次の 2 種類に分ける方針を維持する。

| 等価性 | 意味 |
|---|---|
| 機能的等価性 | 同じ入力 stream と window に対して同じ出力を返す |
| 処理能力等価性 | 同じ throughput requirement に対して同じ capability bound を持つ |

回転等変性は Layer A/B の規約に合わせ、CW を主目標にし、180° / CCW は派生扱いにする。現時点では Prop 型を確定済みであり、大きな証明を増やす前に評価意味論を固める。

---

## 10. 検証手順

Lean 実装を変更する場合は、次の順で検証する。

| タイミング | 手順 |
|---|---|
| 新規 API 追加前 | REPL で `#check` 可能な型に落とす |
| Flow サブモジュール変更後 | `.github/skills/lean-tooling/scripts/build.ps1 -Target S2IL.Flow` |
| Test/Flow 変更後 | `.github/skills/lean-tooling/scripts/build.ps1` |
| 新規 theorem 追加前 | 反例チェック、ゴール形状確認、必要に応じて `lean-theorem-investigator` |

ビルドの正本は build script の diagnostics とし、VS Code Problems は判断材料にしない。

---

## 11. 完了済み項目

完了済みの詳細 TODO はこの計画書では維持しない。現在の成果物は [../../S2IL/Flow.lean](../../S2IL/Flow.lean) の facade と [../../Test/Flow/](../../Test/Flow/) を正本にする。

| 区分 | 状態 |
|---|---|
| C1-DOC | 初期設計、用語整理、基本スループット正本リンク、Layer C 関連インデックス同期まで完了 |
| C1-IMPL | Types / Capability / MachineSpec / Graph / Eval / Examples / Equivariance / Config まで完了 |
| C1-TEST | 基本台数下界、代表 graph、代表出力、設定値の代表検証まで完了 |
| C1-PROOF | port lookup、DAG 判定、等価性と回転等変性の型を分離済み |

次の焦点は、§12 の TODO リストから順に仕様を固定し、小さな Lean API とテストへ落とすことである。

---

## 12. 未解決事項

この節は、今後のアクションを決めるための判断カードである。各項目では、問題の概要、推奨案、代替案、次アクションを分けて記載する。

### 12.1 TODO リスト

この TODO リストは、手戻りを減らすため、評価意味論の境界を先に決め、その後に量・速度・容量・空間制約へ進む順で並べる。

| 順位 | 状態 | TODO | 参照 | 完了条件 |
|---|---|---|---|---|
| 1 | 未着手 | 暗黙 fanout / merge の基本方針を決める | §12.6 / §12.7 | 暗黙接続を WellFormed で禁止するか、明示 policy / node で表すかを決める |
| 2 | 未着手 | 複数入力同期の初期意味論を決める | §12.8 | FIFO zip / tick 同期 / buffer 方式のどれを C-1 標準にするかを決める |
| 3 | 未着手 | 液剤量の単位解釈を決める | §12.2 | `Throughput.amount` と `Fluid.amount` の役割を docstring とテスト方針へ反映する |
| 4 | 未着手 | マシン別スループットの取り込み口を固定する | §12.3 | `FlowConfig` を唯一の Lean 側取り込み口にするかを決め、代表値同期テストを設計する |
| 5 | 未着手 | 速度 tier と通常ベルト基準を決める | §12.5 | C-1 標準を通常ベルト基準に固定するか、tier / multiplier API を追加するかを決める |
| 6 | 未着手 | マシン別容量の扱いを決める | §12.4 | 抽象容量維持 / C-1 外出し / 代表値調査のどれで進めるかを決める |
| 7 | 未着手 | 空間制約の扱いを決める | §12.9 | C-1 から分離するか、抽象 cost だけ取り込むかを決める |

### 12.2 液剤の量単位

**問題の概要**

現在の `FlowAmount.units` は自然数の抽象量であり、Shape の `個/分` と液剤の `L/分` の両方に使える。一方で、評価 API 上の `Fluid.amount` が「1 観測 item に付随する量」なのか、「tick ごとの量」なのか、「throughput としての量」なのかはまだ固定していない。

このままだと、Painter の `30 個/分` と `300 L/分`、CrystalGenerator の `20 個/分` と `400 L/分` のような対応を扱うときに、item 個数と液剤量の換算規則が曖昧になる。

**推奨案: throughput 上の単位として固定し、評価 item 量とは分ける**

`Throughput.amount` では、`belt` を `個/分`、`pipe` を `L/分` と読む。`Fluid.amount` は在庫または観測 item に付随する量として扱い、消費率とは別物にする。Painter / CrystalGenerator の液剤消費は `Capability.consumes` に置く。

利点は、既存の `FlowAmount` と `minMachineCount` を大きく変えずに、処理能力計算を先に安定させられること。欠点は、tick 評価で液剤を実際に減らす段階では別の在庫モデルが必要になること。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: 単位タグを追加 | `FlowUnit.shapeItem` / `FlowUnit.fluidLiter` のような型を加える | 単位不一致を Lean 型または predicate で強く防ぎたい場合 |
| B: 型を分ける | `ShapeRate` と `FluidRate` を別型にする | API の明確さを最優先する場合 |
| C: 有理数量へ拡張 | `Nat` ではなく `Rat` 相当で量を扱う | tick 変換や倍率で端数が必要になった場合 |

**次アクション**

まずは推奨案で設計メモを固め、`Throughput` と `Fluid.amount` の docstring を明確化する。その後、Painter / CrystalGenerator / ColorMixer の消費量テストを追加できるか確認する。

### 12.3 マシン別スループット

**問題の概要**

基本スループット値の正本は game-system overview にあり、Lean 側には `FlowConfig.basic` がある。未解決なのは、正本表の更新をどのように Lean 側へ反映し、`MachineKind` ごとの参照 API をどこまで固定するかである。

値を複数箇所に重複させると、計画書・仕様資料・Lean テストのどれが正しいか分からなくなる。

**推奨案: `FlowConfig` を Lean 側の唯一の取り込み口にする**

ゲーム仕様資料を正本とし、Lean では `FlowConfig` から `MachineKind` ごとの throughput を引く。テストでは代表値だけを `#guard` で固定し、正本表そのものはドキュメントに置く。

利点は、値の参照点が明確になること。欠点は、ゲーム仕様表を更新したときに Lean 側の追随を手作業で確認する必要があること。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: `MachineSpec` に直書き | 各 MachineSpec が基本 throughput を持つ | 設定層を薄くしたい場合。ただし更新に弱い |
| B: 外部データ化 | JSON / TOML などから値を生成する | 値が増え、正本同期を自動化したい場合 |
| C: 当面は代表値のみ | C-1 の検証に必要な値だけを持つ | 仕様確定前の変更を最小にしたい場合 |

**次アクション**

`FlowConfig.basic` の代表値が game-system overview の表と一致することをテストで確認し、未対応 MachineKind がある場合は一覧化する。

### 12.4 マシン別容量

**問題の概要**

`Capability` には `inputCapacity` と `outputCapacity` があるが、マシン別の実ゲーム容量値は未確定である。容量を先に具体化すると、根拠の薄い値が theorem やテストに入り込む危険がある。

また、現在の評価 API は有限 stream の構造評価であり、内部バッファの詰まりや backpressure をまだモデル化していない。

**推奨案: C-1 では抽象容量のまま維持し、具体値は別調査に分離する**

容量フィールドは残すが、代表フローの正しさや必要台数下界は throughput を中心に検証する。容量値が必要になった段階で、ゲーム仕様側に容量の正本表を作ってから `FlowConfig` へ取り込む。

利点は、未確定値を証明に固定しないこと。欠点は、詰まりや停止の解析は後回しになること。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: 容量を 1 tick 分に抽象化 | `capacity = throughput per tick` のように置く | tick 評価と接続したいが実測値がない場合 |
| B: 容量を C-1 から外す | `Capability` から容量を使わず、別層へ送る | API を極小にしたい場合 |
| C: 代表マシンだけ調査 | Painter / Stacker など必要なものだけ先に調べる | 液剤や複数入力の停止条件を早く扱いたい場合 |

**次アクション**

容量を使う theorem / テストを今は追加しない方針を明文化する。容量が必要なユースケースが出たら、正本表の調査タスクへ切り出す。

### 12.5 速度設定

**問題の概要**

C-1 には `SpeedTier` と `FlowConfig.basic` があるが、アップグレード倍率、宇宙ベルトの 2 層 / 3 層差、宇宙パイプ、通常ベルトとの換算をどの粒度で入れるかは未確定である。

`GameConfig` はレイヤ上限など Shape の構成制約を持つため、速度設定と混ぜると責務が曖昧になる。

**推奨案: `FlowConfig` を `GameConfig` から独立させ、通常ベルト基準を C-1 の既定にする**

C-1 の標準検証は通常ベルト 1 本を基準にする。アップグレード倍率や宇宙系搬送は `FlowConfig` の拡張として扱い、必要になるまで評価 API には直接混ぜない。

利点は、C-1 の代表フローを安定させたまま、速度差を後から設定で差し込めること。欠点は、宇宙ベルトや宇宙パイプの本格解析は先送りになること。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: basic のみ固定 | `FlowConfig.basic` 以外をまだ定義しない | C-1 の範囲を絞りたい場合 |
| B: tier ごとに config を列挙 | `basic`, `upgraded`, `space` などを値として持つ | ゲーム内段階をそのまま比較したい場合 |
| C: 倍率関数を持つ | 基本値に multiplier を掛ける API にする | 単調性や倍率証明をしたい場合 |

**次アクション**

通常ベルト基準を C-1 の標準として固定するか決める。固定する場合、宇宙ベルト / 宇宙パイプは拡張項目として別 subsection へ逃がす。

### 12.6 分岐時のストリーム複製 / 分配

**問題の概要**

FlowGraph では 1 つの出力ポートから複数の接続を張れる余地がある。ここで、同じ item が複製されるのか、複数先へ分配されるのか、それとも不正 graph とするのかが未確定である。

物理的なベルトでは、無制限の複製はできない。ここを曖昧にすると、処理能力解析で入力を無料で増やしてしまう可能性がある。

**推奨案: C-1 の暗黙 fanout は禁止し、分岐は明示ノードまたは明示 policy にする**

`WellFormed` では、通常の出力ポートは接続先 1 つまでを既定にする。分配が必要な場合は、将来の Splitter / Distributor などの明示マシン、または `FanoutPolicy` を持つ評価モードとして追加する。

利点は、物理的にありえない複製を避けられること。欠点は、既存代表 graph に暗黙 fanout がある場合は明示構造へ直す必要があること。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: 複製として扱う | 1 出力を全接続先へコピーする | 仕様探索を速くしたい場合。ただし処理能力上は危険 |
| B: round-robin 分配 | 接続先へ順番に item を送る | ベルト分配に近い挙動を抽象化したい場合 |
| C: 比率分配 | throughput を重みで分ける | 処理能力解析を主目的にする場合 |

**次アクション**

まず既存 graph が fanout を使っているか確認する。使っていないなら、暗黙 fanout 禁止を WellFormed の追加条件候補にする。

### 12.7 合流時の順序

**問題の概要**

複数の出力が同じ stream に合流するとき、観測 stream の順序をどう決めるかが未確定である。tick 順、接続順、NodeId 順、入力 arrival 順など、選び方で `FlowGraph.evaluate` の出力が変わる。

処理能力だけを見れば合流は加算で済むが、機能的等価性や代表 I/O では順序が問題になる。

**推奨案: 暗黙 merge を避け、必要な場合は deterministic merge policy を明示する**

通常の評価では、同じ入力ポートへの複数接続や同じ出力 stream への暗黙 merge を WellFormed で禁止する。合流を表したい場合は、明示的な Merge node または `MergePolicy` を導入し、まずは `(tick, source order)` の安定順で評価する。

利点は、評価結果が決定的になること。欠点は、合流を使う graph の記述が少し重くなること。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: NodeId / PortId 順 | 構造順で常に決める | 実装を軽くしたい場合 |
| B: tick 内 round-robin | 同 tick の入力を接続先順に交互化する | 物理寄りの分配と合わせたい場合 |
| C: multiset / bag として扱う | 順序を捨てる | 処理能力等価性だけを扱う場合 |

**次アクション**

機能的等価性で順序を必要とする theorem と、処理能力等価性で順序を捨てられる theorem を分ける。評価 API には deterministic merge policy を入れるか、暗黙 merge 禁止を先に入れる。

### 12.8 レーン同期

**問題の概要**

Stacker / Swapper / Painter / CrystalGenerator などの複数入力マシンでは、入力 item 同士をどの粒度で対応付けるかが必要になる。候補には、同じ tick、各入力 stream の n 番目、FIFO buffer から取り出せた組、lane index の一致などがある。

同期規則がないと、複数入力マシンの評価は代表例では動いても、速度差や片側不足を扱った瞬間に曖昧になる。

**推奨案: C-1 初期意味論では port ごとの FIFO zip とし、throughput 整合性を別条件にする**

各入力ポートの stream を FIFO として読み、n 番目同士を組にする。速度差や不足がある場合は短い側で停止または評価不能にし、処理能力側では必要 throughput が満たされることを別に確認する。

利点は、代表フローと複数入力マシンを自然に扱えること。欠点は、tick 内の厳密な arrival timing や buffer 容量は表現しないこと。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: tick 完全同期 | 同じ tick にある item だけを組にする | 離散時間物理を重視する場合 |
| B: FIFO + buffer 容量 | 入力ごとに buffer を持ち、揃ったら処理する | 停止や詰まりを扱いたい場合 |
| C: lane-indexed stream | レーンごとの stream を型に入れる | 宇宙ベルトや多レーン解析へ進む場合 |

**次アクション**

まず Stacker / Swapper の代表評価を FIFO zip として仕様化できるか確認する。その上で、片側不足・速度差・空 stream の扱いをテストケースにする。

### 12.9 空間制約

**問題の概要**

現在の必要マシン数は、処理能力の下界であり、ベルト、ランチャー、配置面積、配線長、建物 footprint を含まない。したがって「必要台数 8 台」や「30 台」は、実際の敷設可能性や最小面積を意味しない。

MAM 完全性や実機再現へ進む段階では空間制約が重要になるが、C-1 の評価意味論と同時に入れると問題が大きくなりすぎる。

**推奨案: 空間制約は C-1 から分離し、処理能力下界とは別計画にする**

C-1 では、FlowGraph が加工意味と throughput bound を表すことに集中する。空間制約は、必要になった段階で Layer C の別計画または Layer D 寄りの配置モデルとして切り出す。

利点は、C-1 の証明対象を保てること。欠点は、実ゲーム配置としての完全性はまだ主張できないこと。

**代替案**

| 案 | 内容 | 向いている場合 |
|---|---|---|
| A: 抽象コストだけ追加 | 各 machine に面積 cost を持たせ、合計だけ見る | 配置までは不要だが規模比較をしたい場合 |
| B: grid placement を導入 | 座標、占有領域、接続可能性を持つ | 実ゲーム配置の正しさを証明したい場合 |
| C: launchers だけ追加 | ベルト / パイプ launcher の数だけ数える | 宇宙プラットフォーム間搬送を先に扱いたい場合 |

**次アクション**

この資料では「C-1 の台数下界は空間制約を含まない」と明記して維持する。空間制約が必要なユースケースが具体化したら、独立計画として起票する。
