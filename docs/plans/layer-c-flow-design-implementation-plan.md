# Layer C Flow 設計/実装計画

> 作成日: 2026-05-16
> 最終更新: 2026-05-16

## Current Focus

| 項目 | 値 |
|---|---|
| 対象 | Layer C / C-1 Shape Processing Flow |
| 初期方針 | C-1 を先行し、C-2 は設計に留める |
| 実装モデル | 型付きパイプライン / 合成 DSL |
| 次の実装単位 | ゲーム内の特徴的な加工フロー例の追加 |

---

## 実装状況

| 区分 | 状態 | 主な成果物 |
|---|---|---|
| C-1a Flow Core | 実装済み | `Flow α β` / `Flow.eval` / primitive wrappers |
| C-1b Product Flow | 実装済み | `Flow.swap` / `Flow.dup` / `Flow.pairMap` / `Flow.dropFirst` / `Flow.dropSecond` / `Flow.assocLeft` / `Flow.assocRight` / product congruence |
| C-1c E/W・象限抽出 | 初期 theorem 化済み | `extractNE` / `extractSE` / `extractSW` / `extractNW` と `shapeOnlyDirection` 仕様 |
| C-1d 生成フロー | 表現基盤実装済み | `swapShapes` / `mix` / `paintWith` / `crystallizeWith` / `trash` / `stackThenPaint` / `swapThenStack` / `mixThenPaint` / `mixThenCrystallize` |
| C-2 Wires | 設計のみ | 非循環の純粋ネットワーク方針 |

非Wireの加工フローは、Shape 系入力、Color 系入力、product 入出力、固定ソース、片側出力の破棄を組み合わせて一通り表現できる段階に入った。次の焦点は、ゲーム内の特徴的な加工フローを `Flow.Examples` と `Test.Flow.Examples` に追加し、必要に応じて settled / gravity theorem を接続することである。

---

## 目的

Layer C は、Layer A/B で定義・検証した個別加工操作を、Shapez2 の加工ラインとして組み合わせる層である。本計画では、MAM 完全性へ進む前段として、加工装置の接続、評価、等価性、代表フロー検証を Lean で扱える形にする。

Layer C は二つに分ける。

| 領域 | 方針 |
|---|---|
| C-1 Shape Processing Flow | 初期実装対象。既存 `S2IL.Operations` を typed flow として合成する。 |
| C-2 Wires and Logic Flow | 今回は設計方針のみ。C-1 安定後、非循環の純粋ネットワークとして実装する。 |

---

## 決定事項

- C-1 Shape Flow を先行し、C-2 は設計だけに留める。
- Flow は一般 DAG / 任意グラフではなく、型付きパイプライン / 合成 DSL として始める。
- `Flow.eval` を唯一の実行意味論にする。
- フロー等価性は外延的等価性、すなわち `∀ x, Flow.eval f x = Flow.eval g x` を正本にする。
- `Shape.cut` のような多出力操作は product 型で扱う。
- `eastHalf` / `westHalf` / `combineHalves` / `cut` / `halfDestroy` は E/W 参照操作であり、CW 等変性を要求しない。180° 版と成分 swap 版を別系統で扱う。
- settled invariant は初期 DSL の型には持たせず、後続 theorem 層で扱う。
- C-2 の将来評価意味論は、まず非循環の純粋ネットワークに限定する。

---

## スコープ

### 含める

- C-1 の Flow 型、評価関数、primitive operation node。
- `id` / composition / product 操作による型付き合成。
- Flow の外延的等価性と congruence 補題。
- CW-safe operation の等変性合成、および E/W 参照操作の 180° 系。
- MAM へつながる代表フロー、特に象限抽出の検証準備。
- C-2 の将来設計として、WireSignal ベースの非循環ネットワーク方針。

### 含めない

- 任意 DAG / 任意グラフの接続検証。
- ベルト throughput、tick、遅延、レーン、搬送速度。
- Machine 状態や建物配置そのもののシミュレーション。
- 信号による動的分岐や Belt Filter / Pipe Gate の統合。
- cycles / feedback / fixed point を含む wire network。
- MAM 完全性本体。

---

## 設計方針

### Flow の核

初期案は generic な型付き combinator とする。最初の実装では Shape / Color / `GameConfig` など
現行 S2IL の値を扱うため `Type 0` に固定し、必要になった時点で universe-polymorphic 化を検討する。

```lean
namespace S2IL

inductive Flow : Type 0 → Type 0 → Type 1 where
  | id : Flow α α
  | prim : (α → β) → Flow α β
  | comp : Flow α β → Flow β γ → Flow α γ
  | first : Flow α β → Flow (α × γ) (β × γ)
  | second : Flow α β → Flow (γ × α) (γ × β)
  | fanout : Flow α β → Flow α γ → Flow α (β × γ)

namespace Flow

def eval : Flow α β → α → β := ...

end Flow
end S2IL
```

この形なら、`Shape → Shape` の単純パイプラインだけでなく、`Shape.cut : Shape → Shape × Shape`、`Shape.stack : Shape → Shape → GameConfig → Shape` のような多入出力操作も product 型で扱える。

primitive node は whitelist 方針で公開する。最初の候補は次の通り。

| primitive | 既存 API | 備考 |
|---|---|---|
| rotate CW / 180 / CCW | `Shape.rotateCW` / `Shape.rotate180` / `Shape.rotateCCW` | Kernel / Transform |
| half destroy | `Shape.halfDestroy` | E/W 参照、CW ではなく 180° 系 |
| cut | `Shape.cut` | `Shape → Shape × Shape` |
| swapper | `Shape.swap` | `Shape × Shape → Shape × Shape` |
| combine halves | `Shape.combineHalves` | product 入力で扱う |
| color mixer | `Operations.mix` | `Color × Color → Color` |
| paint with input color | `Shape.paint` | `Shape × Color → Shape` |
| crystallize with input color | `Shape.crystallize` | `Shape × Color → Shape` |
| paint | `Shape.paint` | 色パラメータを固定した primitive |
| crystallize | `Shape.crystallize` | 色パラメータを固定した primitive |
| trash | `Shape.trash` | `Shape → Unit` として「出力なし」を表す primitive |
| gravity | `Shape.gravity` | Layer B の total function として呼ぶ |
| stack | `Shape.stack` | `GameConfig` を固定した primitive |
| pin push | `Shape.pinPush` | `GameConfig` を固定した primitive |

### 評価意味論

`Flow.eval` は純粋・全関数として定義する。Flow 側では gravity の fuel や tick を再導入せず、Layer B が公開している `Shape.gravity` / `Shape.stack` / `Shape.pinPush` をそのまま呼ぶ。

Machine facade は現状 placeholder のため、C-1 初期実装は `S2IL.Machine` を経由しない。Layer D で Machine / Wire と接続する段階になってから adapter を追加する。

### フロー等価性

フロー等価性は外延的に定義する。

```lean
def Flow.Equivalent (f g : Flow α β) : Prop :=
  ∀ x, Flow.eval f x = Flow.eval g x
```

最初に整備する補題は以下。

- reflexive / symmetric / transitive
- composition congruence
- product congruence
- `Flow.eval` の simp 補題
- primitive wrapper が既存 operation と一致すること

構造同値やグラフ同型は扱わない。

### 等変性

Layer A/B の単一チェーン原則を引き継ぐ。ただし Flow 全体へ一律に CW 等変性を要求しない。

| 分類 | 方針 |
|---|---|
| CW-safe primitive | 既存の `rotateCW_comm` を Flow 合成へ持ち上げる。 |
| 180° / CCW 系 | CW-safe primitive では CW 版から機械的に導出する。 |
| E/W 参照操作 | `eastHalf` / `westHalf` / `combineHalves` / `cut` / `halfDestroy` は CW 等変性を持たない。180° 版と成分 swap 版だけを証明対象にする。 |

Flow 側では、成立する flow にだけ性質を付与するため、次のような述語を導入する。

```lean
def Flow.CWEquivariant (f : Flow Shape Shape) : Prop :=
  ∀ s, Shape.rotateCW (Flow.eval f s) = Flow.eval f (Shape.rotateCW s)

def Flow.HalfTurnEquivariant (f : Flow Shape Shape) : Prop :=
  ∀ s, Shape.rotate180 (Flow.eval f s) = Flow.eval f (Shape.rotate180 s)
```

product 型の flow には、成分 swap を含む専用 predicate を別に用意する。

---

## モジュール構成案

```text
S2IL/Flow.lean
S2IL/Flow/
  Defs.lean
  Equivalence.lean
  Equivariance.lean
  Examples.lean
  Internal/
```

| ファイル | 役割 |
|---|---|
| `S2IL/Flow.lean` | Layer C-1 facade。公開 API と目次を集約する。 |
| `S2IL/Flow/Defs.lean` | `Flow α β`、primitive wrappers、`Flow.eval`。 |
| `S2IL/Flow/Equivalence.lean` | 外延的等価性と congruence 補題。 |
| `S2IL/Flow/Equivariance.lean` | CW / 180° / E-W 参照操作の性質を Flow に持ち上げる。 |
| `S2IL/Flow/Examples.lean` | 象限抽出など MAM へつながる代表フロー。 |
| `S2IL/Flow/Internal/` | 補助補題が肥大化した時点で作る。 |

root facade `S2IL.lean` には `import S2IL.Flow` を追加する。

---

## 実装マイルストーン

### C-1a: Flow Core

| 成果物 | 内容 |
|---|---|
| `Flow α β` | `id` / `prim` / `comp` / product combinator の最小核 |
| `Flow.eval` | 合成 DSL の評価関数 |
| primitive wrappers | rotate / paint / gravity など単純な `Shape → Shape` から開始 |
| smoke tests | `Test/Flow/Defs.lean` で `#guard` と `example` |

### C-1b: Product Flow

| 成果物 | 内容 |
|---|---|
| cut flow | `Shape → Shape × Shape` |
| combine halves flow | `Shape × Shape → Shape` |
| stack flow | `Shape × Shape → Shape`、`GameConfig` 固定 |
| equivalence 補題 | product congruence と eval simp |

### C-1c: E/W 系と象限抽出

| 成果物 | 内容 |
|---|---|
| half-destroy chain | `halfDestroy` / rotate / `halfDestroy` の代表 flow |
| 具体例検証 | 小さい shape で `#guard` / REPL smoke run |
| 象限抽出定理 | `docs/shapez2/mam.md` の説明を現行方向定義と照合してから theorem 化 |

注意: `Shape.halfDestroy = Shape.eastHalf` であり、E/W 参照操作は CW 等変性を持たない。そのため、MAM 文書の NE 抽出説明は、定理名・定理文に落とす前に現行 `Direction` と `Layer.eastHalf` の定義で再確認する。

### C-1d: 生成フロー

| 成果物 | 内容 |
|---|---|
| paint flow | 色パラメータ固定の着色 flow |
| crystallize flow | 結晶生成 flow |
| stack / pin push flow | vanilla4 / vanilla5 での代表例 |
| settled theorem | 必要に応じて Flow eval 出力に Layer B theorem を接続 |

### C-2: Wires 設計の後続実装

| 項目 | 初期方針 |
|---|---|
| network | 非循環の純粋 `WireNetwork` |
| signal | 既存 `WireSignal` の `off` / `boolean` / `shape` / `color` を使う |
| gate 候補 | AND / OR / NOT / XOR / comparison / mux |
| evaluation | 入力信号から出力信号への決定的評価 |
| 対象外 | cycles / fixed point / synchronous tick / conflict propagation |

---

## 不確定要素と決定ゲート

| 論点 | 初期判断 | 決定タイミング |
|---|---|---|
| 象限抽出の具体式 | `#guard` / REPL で現行実装と照合する | C-1c 着手前 |
| `Flow α β` の universe 設計 | generic 型で開始する | C-1a 実装前に短い prototype で確認 |
| settled invariant | theorem 層に分離する | C-1d で必要になった時点 |
| `GameConfig` 標準 | vanilla4 / vanilla5 をテスト対象にする | stack / pinPush flow 追加時 |
| C-2 gate set | comparison と mux を含める可能性が高い | C-2 実装直前 |
| Machine 接続 | Layer D adapter として扱う | D-1 着手時 |

---

## 検証方針

- 既存 API 参照は facade 経由に限定する。
- 新規公開 API は REPL `#check` / `example ... := by` で型を確認してから定着させる。
- 代表フローは theorem 化前に小さい concrete shape の `#guard` で挙動を確認する。
- C-1 core 実装後は `.github/skills/lean-tooling/scripts/build.ps1` を実行する。
- Test 追加後は `.github/skills/lean-tooling/scripts/build.ps1 -Target Test` を実行する。

---

## 参照

| ファイル | 用途 |
|---|---|
| [MILESTONES.md](MILESTONES.md) | Layer C/D の高レベル目標 |
| [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) | facade / Internal / MECE / 等変性原則 |
| [../shapez2/game-system-overview.md](../shapez2/game-system-overview.md) | Shape Processing と安定状態の仕様 |
| [../shapez2/mam.md](../shapez2/mam.md) | MAM の象限抽出・信号処理・物理生産 |
| [../../S2IL/Operations.lean](../../S2IL/Operations.lean) | C-1 が参照する加工操作 facade |
| [../../S2IL/Operations/Cutter.lean](../../S2IL/Operations/Cutter.lean) | E/W 参照操作と 180° 等変性 |
| [../../S2IL/Wires.lean](../../S2IL/Wires.lean) | C-2 Wires skeleton |
