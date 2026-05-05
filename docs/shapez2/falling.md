# 落下 (Falling / Gravity)

Shapez2 における **落下 (Falling)** 操作に関する厳密な仕様書。

---

## 1. 概要

**落下** とは、支えのない（浮遊している）シェイプの塊が、支えを得るまで下方に移動する物理的な挙動である。
落下は以下の操作の結果として発生しうる:

| トリガー | 発生状況 |
|---|---|
| **積み重ね (Stacking)** | 上シェイプが下シェイプの上に落とされ、空の象限を通り抜けて固い面に当たるまで落下する |
| **切断 (Cutting)** | 切断により支えを失った象限が落下する |
| **ピン押し (Pin Pushing)** | ピン押しがレイヤ上限超過を引き起こし、廃棄後に支えを失った象限が落下する |

落下処理には結晶の **砕け散り (Shatter)** が連動する。
脆弱な結晶が落下対象に含まれる場合、結晶結合クラスタ全体が砕け散った後に落下処理が実行される
（[結晶砕け散りとの連携](#8-結晶砕け散り-shatter-との連携) を参照）。

---

## 2. 構造結合 (Structural Bond)

### 2.1 結合能力 (Bond Capability)

象限がシェイプの「塊」を形成する能力を **結合能力 (Bond Capability)** と呼ぶ。
結合能力を持つシェイプ種別は、他の結合能力を持つ隣接象限と一体の塊を形成できる。

| Quarter コンストラクタ | 結合能力 | 備考 |
|---|---|---|
| `Quarter.empty` | なし | 空 |
| `Quarter.pin` | **なし** | ピンは他と塊を形成しない（孤立した落下単位） |
| `Quarter.crystal color` | **あり** | 結晶は通常パーツと同様に塊を形成する |
| `Quarter.colored part color` | **あり** | circle, rectangle, star, windmill |

> **結晶結合 (Crystal Bond) との違い**: 結晶結合（[`crystal-shatter.md`](crystal-shatter.md) 参照）は砕け散りの伝播範囲を決定するための結合であり、**結晶同士** のみが対象で色や位置に追加の制約がある。一方、構造結合はシェイプ種別・色を **問わず**、結合能力を持つ全ての非空象限が対象であり、落下時の塊（構造クラスタ）を決定する。

#### Lean での実装

```lean
def Quarter.canFormBond : Quarter → Bool
    | empty     => false
    | pin       => false
    | crystal _ => true
    | colored _ _ => true
```

### 2.2 構造結合の条件

2つの象限位置 A, B が **構造結合 (Structurally Bonded)** している条件:

1. A と B がともに **結合能力を持つ**（`canFormBond = true`）
2. A と B が **隣接** している（以下のいずれか）:
   - **同レイヤ内隣接**: 同一レイヤ内で方角が円環上で隣り合う（[`adjacency.md`](adjacency.md#3-同レイヤ内の隣接関係) 参照）
   - **上下レイヤ間隣接（垂直隣接）**: 同方角かつ垂直に隣接するレイヤ（[`adjacency.md`](adjacency.md#4-上下レイヤ間の隣接関係垂直隣接) 参照）

> **注意**: 結合能力の判定にシェイプ種別や色の一致は **不要** である。例えば `Circle(Red)` と `Star(Blue)` が隣接していれば構造結合する。

---

## 3. 構造クラスタ (Structural Cluster)

### 3.1 定義

構造結合の **推移閉包** にもとづく連結成分を **構造クラスタ (Structural Cluster)** と呼ぶ。
すなわち、構造結合の連鎖で互いに到達可能な象限の集合が1つの構造クラスタを形成する。

- 結合能力のない象限（空、ピン）は構造クラスタに含まれない
- **ピン** は常に **孤立した落下単位** として扱われ、構造クラスタには参加しない
- 結合能力を持つ象限が隣接する結合能力を持つ象限と接触していない場合、その象限は **サイズ 1** の構造クラスタとなる

### 3.2 例

| シェイプコード | 構造クラスタ | 説明 |
|---|---|---|
| `CrCr----:--RgRg--` | {L1:NE(Cr), L1:SE(Cr), L2:SE(Rg), L2:SW(Rg)} — 1 クラスタ | L1:SE(Cr) と L2:SE(Rg) が垂直隣接で構造結合し、全体が繋がる |
| `CrCr----:----RgRg` | {L1:NE(Cr), L1:SE(Cr)}, {L2:SW(Rg), L2:NW(Rg)} — 2 クラスタ | L1 と L2 が同方角で垂直接触する象限がないため独立 |
| `Cr--Rg--` | {L1:NE(Cr)}, {L1:SW(Rg)} — 2 クラスタ | NE と SW は対角で非隣接 |
| `CrCrCrCr` | {L1:NE, L1:SE, L1:SW, L1:NW} — 1 クラスタ | 4象限すべてが円環隣接で構造結合 |
| `P-Cr----` | {L1:SE(Cr)} — 1 クラスタ + L1:NE(P) — 孤立ピン | ピンはクラスタに参加しない |

### 3.3 アルゴリズム

シェイプは最大 `config.maxLayers` レイヤ × 4 象限（vanilla4 で 16、vanilla5 で 20）であるため、
結合関係の反射推移閉包を有限回反復で求める素朴な算法で十分である（証明側は Mathlib `Relation.ReflTransGen` を利用し、実装側は有限集合の反復で計算する）。

---

## 4. 接地 (Grounding)

### 4.1 接地接触 (Grounding Contact)

2つの非空象限位置 A, B の間に **接地接触 (Grounding Contact)** があるとは、以下のいずれかの条件を満たすことである:

#### 垂直方向の接地接触

| 条件 | 説明 |
|---|---|
| A と B が **同方角** に位置する | 例: 両方とも NE |
| A と B が **垂直に隣接するレイヤ** にある | 例: L1 と L2 |
| A と B がともに **非空** である | ピンを含む全てのシェイプ種別が対象 |

#### 水平方向の接地接触

| 条件 | 説明 |
|---|---|
| A と B が **同一レイヤ** にある | 例: 両方とも L1 |
| A と B の方角が **隣接** している | `Direction.adjacent` = true |
| A と B がともに **非空** である | 空の象限は接地接触を持たない |
| A と B がともに **ピンでない** | ピンは水平方向の接地接触を形成しない |

> **ピンの特殊性**: ピンは **垂直方向では** 接地接触を伝播するが、**水平方向では** 接地接触を伝播しない。これはピンが「支柱」として上下方向の支持のみを提供する性質を反映している。

### 4.2 接地 (Grounded) の定義

非空象限が **接地 (Grounded)** しているとは、以下のいずれかを満たすことである:

1. その象限が **レイヤ 0（最下層）** に位置し、非空である（**直接接地**）
2. その象限から **接地エッジ (Grounding Edge)** の連鎖を辻って、レイヤ 0 の非空象限に到達できる（**間接接地**）

接地していない非空象限は **非接地 (Ungrounded)** である。

**接地エッジ (Grounding Edge)** は、以下のいずれかを満たす位置ペア (A, B) である:

1. **上方向接地接触 (Upward Grounding Contact)**: A と B が接地接触（§4.1）を満たし、かつ `A.layer ≤ B.layer`（上方向または同層）
2. **構造結合 (Structural Bond)**: A と B が構造結合（§2.2）を満たす（方向制約なし、双方向）

Lean での実装:

```lean
def groundingEdge (s : Shape) (a b : QuarterPos) : Bool :=
    isUpwardGroundingContact s a b || isStructurallyBonded s a b
```

> **構造クラスタと接地の関係**: 構造結合が接地エッジに含まれるため、**構造クラスタ内のいずれかの象限が接地していれば、クラスタ全体が接地する**。クラスタは剛体として振る舞うため、上位レイヤ経由で接地済みのメンバーから、構造結合を通じて下位レイヤのメンバーへも接地が伝播する。
>
> **ピンの咫外**: ピンは `canFormBond = false` であるため構造結合を形成できず、**接地エッジの構造結合側の恩恵を受けない**。ピンの接地は上方向接地接触のみに依存する。したがって、垂直方向で上位レイヤから下方向にピンへ接地が伝播することはない。

> **例**: `Rr------:RgP-P-P-:RuRuRuRu` において、L1:SE のピンは L0:NE(Rr) → L1:NE(Rg) → L2:NE(Ru) → L2:SE(Ru) → L1:SE(P) という下方向の垂直接触を含むパスでは接地されない。L2:SE(Ru) と L1:SE(P) の間には上方向接地接触がなく（下方向）、かつピンは構造結合を形成できないため、L1:SE は非接地（浮遊）と判定される。

### 4.3 接地の例

| シェイプコード | 象限 | 接地状態 | 説明 |
|---|---|---|---|
| `Cr------` | L1:NE(Cr) | 接地 | レイヤ 0 に位置する |
| `--------:Cr------` | L2:NE(Cr) | 非接地 | L1:NE が空のため接地接触がない |
| `CrCr----:--RgRg--` | L2:SE(Rg) | 接地 | L2:SE → L1:SE(Cr) への垂直接地接触 |
| `CrCr----:--RgRg--` | L2:SW(Rg) | 接地 | L2:SW ← L2:SE(Rg) への水平接地接触（Rg は非ピン）→ L1:SE(Cr) |
| `P-------` | L1:NE(P) | 接地 | レイヤ 0 のピンは直接接地 |
| `P-------:P-------` | L2:NE(P) | 接地 | L2:NE(P) → L1:NE(P) への垂直接地接触 |
| `Cr------:RgP-----` | L2:NE(Rg) | 接地 | L2:NE(Rg) → L1:NE(Cr) への垂直接地接触 |
| `Cr------:RgP-----` | L2:SE(P) | **非接地** | L1:SE が空（垂直接触なし）、L2:NE(Rg) とは水平隣接だがピンは水平接触不可 |
| `CrCrCrCr:P-------:RgRgRgRg` | L3:NE(Rg) | 接地 | L3:NE → L2:NE(P) → L1:NE(Cr) の垂直接地接触チェーン |
| `--CrCr--:--------:--RgRg--` | L3:SE(Rg) | **非接地** | L2 が全空のため垂直接地接触が途切れる |

---

## 5. 浮遊 (Floating)

### 5.1 浮遊の判定

**浮遊 (Floating)** とは、非空象限またはその集合が接地していない状態を指す。

落下処理の対象となる単位は以下の2種類:

| 種類 | 定義 |
|---|---|
| **浮遊クラスタ** | 構造クラスタ内の **全ての象限** が非接地である |
| **浮遊ピン** | 接地していない個々のピン |

これらを総称して **落下単位 (Falling Unit)** と呼ぶ。

> **注意**: 構造クラスタの **一部** の象限だけが非接地で、他の象限が接地しているケースでは、クラスタ全体が接地している扱いとなり、浮遊とは見なされない。クラスタは一体の剛体として振る舞う。

### 5.2 浮遊判定の例

| シェイプコード | 落下単位 | 説明 |
|---|---|---|
| `--------:Cr------` | {L2:NE(Cr)} — 1 浮遊クラスタ | L1 全空、L2:NE が非接地 |
| `--------:--Cr--Cr` | {L2:SE(Cr)}, {L2:NW(Cr)} — 2 浮遊クラスタ | 各象限が独立した非接地クラスタ |
| `CrCr----:----RgRg` | {L2:SW(Rg), L2:NW(Rg)} — 1 浮遊クラスタ | L1 のクラスタは接地。L2 は非接地 |
| `CrCr----:--RgRg--` | なし | L1:SE(Cr) → L2:SE(Rg) の垂直接地接触でクラスタ全体が接地 |
| `Cr------:RgP-----` | {L2:SE(P)} — 1 浮遊ピン | L2:NE(Rg) は接地、L2:SE(P) は非接地のピン |

---

## 6. 落下処理 (Gravity Process)

### 6.1 Wave Gravity の原則

落下処理は **Wave Gravity**（波面型同時落下モデル）として定義する。
Wave Gravity は、現在のシェイプにおける非接地な非空象限をすべて同時に 1 レイヤ下げ、この 1 tick の処理を安定するまで反復するモデルである。

このモデルでは、落下対象を順序付けない。各 tick の開始時点で `IsGrounded` を再評価し、その時点で接地していない象限だけを動かす。
長距離の着地距離計算、落下単位のソート、逐次 accumulator による上書き規則は仕様に含めない。

### 6.2 浮遊位置

1 tick で移動する位置を **浮遊位置 (Floating Position)** と呼ぶ。

```lean
def FloatingPos (s : Shape) (p : QuarterPos) : Prop :=
  p ∈ QuarterPos.allValid s ∧
  ¬ (QuarterPos.getQuarter s p).isEmpty ∧
  ¬ IsGrounded s p
```

`FloatingPos s p` なら `p` は layer 0 にはない。layer 0 の非空象限は直接接地するためである。したがって、`p = (l, d)` の 1 レイヤ下の位置 `p.down = (l - 1, d)` が定義できる。

§5 の浮遊クラスタ / 浮遊ピンは、どの象限が `FloatingPos` になるかを説明するための判定概念として残る。アルゴリズム自体は、cluster と pin を別処理せず、`FloatingPos` を満たす象限を同じ規則で動かす。

### 6.3 1 tick のアルゴリズム

`waveStep` は以下の atomic 操作である。

```
入力: シェイプ S
出力: 1 tick 後のシェイプ S'

1. F = { p | FloatingPos S p } を現在の S から計算する
2. F に属する全位置を空にする
3. 各 p ∈ F について、S[p] の値を p.down に同時に書き込む
4. F に属さず、どの p.down にもならない位置は元の値を保つ
```

この操作は「同時」であり、列挙順を意味に含めない。実装上は有限リストを用いて計算してもよいが、仕様上の意味は `F` から `p.down` への部分写像による一括更新である。

### 6.4 `Shape.gravity` のアルゴリズム

落下処理全体は `waveStep` を有限回反復し、最後に正規化する。

```lean
def waveGravityCore (fuel : Nat) (s : Shape) : Shape :=
  Nat.iterate waveStep fuel s

def Shape.gravity (s : Shape) : Shape :=
  (waveGravityCore s.length s).normalize
```

`fuel = s.length` で十分である。floating な非空象限は各 tick で layer index を 1 減らし、layer 0 に到達すると直接接地する。既に接地している象限は動かないため、初期シェイプの高さを超える回数の tick 後には浮遊位置が残らない。

### 6.5 Atomic shift の安全性

`p ∈ F` の移動先 `p.down` が旧シェイプで非空だったとしても、次のいずれかである。

- `p.down` も `F` に属しており、同じ tick で空けられる
- `p.down` が接地済みなら、`p.down` から `p` への垂直接地接触により `p` も接地しているため、`p ∈ F` と矛盾する

また、同じ方角にある 2 つの異なる位置 `p`, `q` について `p.down = q.down` は成立しない。したがって、同時書き込み同士が同じ位置を取り合うこともない。

この安全性は cluster / pin の場合分けではなく、`FloatingPos` と `IsGrounded` の定義から導く。

### 6.6 落下処理の例

#### 例 1: 基本的な落下

```
初期: --------:Cr------

tick 0:
  L2:NE(Cr) は非接地なので F に入る
  L2:NE → L1:NE へ移動

結果: Cr------
```

#### 例 2: 独立した浮遊象限の同時落下

```
初期: --------:--Cr--Cr

tick 0:
  L2:SE(Cr), L2:NW(Cr) はどちらも非接地
  両方を同時に 1 レイヤ下げる

結果: --Cr--Cr
```

#### 例 3: 接地済み cluster は動かない

```
初期: CrCr----:--RgRg--

構造クラスタ: {L1:NE(Cr), L1:SE(Cr), L2:SE(Rg), L2:SW(Rg)}
  ※ L1:SE(Cr) と L2:SE(Rg) が垂直構造結合

L1 側が直接接地しているため、構造クラスタ全体が接地している。
FloatingPos は存在しない。

結果: CrCr----:--RgRg--（変化なし）
```

#### 例 4: 同列 stack の同時落下

```
初期: --------:P-------:Cr------

tick 0:
  L2:NE(P) と L3:NE(Cr) はどちらも非接地
  P は L1:NE へ、Cr は L2:NE へ同時に移動

結果: P-------:Cr------
```

下側の P の旧位置は Cr の移動先だが、P 自身も同じ tick で下へ移動するため、上書きや処理順は発生しない。

#### 例 5: tick ごとの再評価

```
初期: CrCr----:--------:--RgRg--:--------:----SbSb

tick 0:
  L3 の Rg cluster と L5 の Sb cluster はどちらも非接地
  両方を同時に 1 レイヤ下げる
  中間: CrCr----:--RgRg--:--------:----SbSb

tick 1:
  Rg cluster は L1 の Cr に支えられて接地済み
  Sb cluster だけが非接地なので 1 レイヤ下げる

結果: CrCr----:--RgRg--:----SbSb
```

Wave Gravity は各 tick の現在状態で `FloatingPos` を再計算する。先に誰かを処理するのではなく、同時移動と再評価の反復で積み重なりを表現する。

---

## 7. 性質 (Properties)

落下処理の定義から導かれる主要な性質:

### 7.1 終了性 (Termination)

落下処理は必ず有限ステップで完了する。

**理由**: floating な非空象限は各 `waveStep` で layer index を 1 減らす。layer 0 に到達した象限は直接接地し、それ以後は動かない。したがって `s.length` 回の反復後には浮遊位置が残らない。

### 7.2 決定性 (Determinism)

落下処理の結果は入力シェイプに対して一意に定まる。

**理由**: 各 tick の移動対象 `F = { p | FloatingPos S p }` は現在のシェイプ `S` から一意に決まる。`waveStep` は `F` から `p.down` への同時写像として定義され、処理順を持たない。

### 7.3 冪等性 (Idempotency)

`gravity(gravity(S)) = gravity(S)`

落下後のシェイプには浮遊位置が存在しないため、再度落下処理を適用しても変化しない。正確な等式として扱う場合は、末尾空レイヤの除去を考慮し、正規化済みシェイプを基準にする。

### 7.4 レイヤ数不増 (Layer Count Non-Increase)

落下処理によりレイヤ数が増加することはない。各 `waveStep` は象限を下方にのみ移動させ、新しい上位レイヤを追加しない。

### 7.5 正規化との関係

落下により最上位レイヤが全て空になる場合がある。落下処理の最終ステップで `Shape.normalize` を適用し、末尾の空レイヤを除去する。

### 7.6 形式検証方針

Wave Gravity の主定理は、層数を vanilla4 に限定せずに証明する方針とする。

| 補題 / 性質 | 方針 |
|---|---|
| `waveStep` の atomic shift 仕様 | `FloatingPos` と `p.down` の関係として証明 |
| `waveStep` の安全性 | `p.down` が非空なら接地済みでないことから導く |
| `waveStep` の接地保存 | 接地パスが floating 位置を通らないことへ還元 |
| `waveGravityCore` の終了性 | floating height の減少で証明 |
| `Shape.gravity.isSettled` | `s.length` 回の反復後に浮遊位置がないことから導く |
| `Shape.gravity.rotateCW_comm` | `FloatingPos` と `down` の CW 可換性から導く |

---

## 8. 結晶砕け散り (Shatter) との連携

落下のトリガーとなる操作において、結晶の砕け散りが先行して発生する場合がある。

### 8.1 実行順序

落下を伴う操作の実行順序は以下の通り:

```
1. 砕け散り (Shatter)
   - 落下対象となる脆弱 (Fragile) な象限を識別する
   - それらが属する結晶結合クラスタ（Crystal Bond Cluster）全体を砕け散らせる
   - 砕け散った象限は Quarter.empty に置き換わる
   （詳細は crystal-shatter.md 4.1 節を参照）

2. 構造クラスタの算出
   - 砕け散り後のシェイプに対して構造クラスタを算出する
   - 砕け散りにより空になった象限は構造結合を持たないため、
     クラスタが分割される場合がある

3. 落下処理 (Gravity)
   - 本仕様の 6 節のアルゴリズムに従って実行する
```

### 8.2 落下対象と砕け散り対象の関係

| 操作 | 砕け散りの基準 | 落下対象の基準 |
|---|---|---|
| **積み重ね** | 落下対象の脆弱象限のクラスタ | 砕け散り後の `FloatingPos` |
| **切断** | 東西に跨がるクラスタ | 砕け散り + 切断後の `FloatingPos` |
| **ピン押し** | 廃棄レイヤの脆弱象限のクラスタ | 砕け散り後の `FloatingPos` |

### 8.3 Lean コードとの対応

| 概念 | Lean 定義 | ファイル |
|---|---|---|
| 砕け散り対象の算出（落下時） | `Shape.shatterTargetsOnFall` | [`Shatter.lean`](../../S2IL/Operations/Shatter.lean) |
| 砕け散りの適用（落下時） | `Shape.shatterOnFall` | 同上 |
| 砕け散り対象の算出（切断時） | `Shape.shatterTargetsOnCut` | 同上 |
| 砕け散りの適用（切断時） | `Shape.shatterOnCut` | 同上 |
| 構造結合・接地・安定状態 | `IsStructurallyBonded`, `IsGrounded`, `IsSettled` | [`Settled.lean`](../../S2IL/Operations/Settled.lean) |
| 落下処理 | `Shape.gravity` | [`Gravity.lean`](../../S2IL/Operations/Gravity.lean) |
| 落下処理の回転等変性 | `Shape.gravity.rotateCW_comm` | [`Gravity.lean`](../../S2IL/Operations/Gravity.lean) |

---

## 9. スコープ制限

本仕様では以下を **対象** とする:
- 落下（重力）操作に関するルールの厳密な定義
- 構造結合・構造クラスタ・接地・浮遊の定義
- 結晶砕け散りとの連携順序

本仕様では以下を **範囲外** とする:
- **積み重ね操作の全体定義** — 落下はそのサブプロセスであり、積み重ね全体は別タスク (MILESTONES 1-2-9)
- **切断操作の全体定義** — 別タスク (MILESTONES 1-2-1 〜 1-2-3)
- **ピン押し操作の全体定義** — 別タスク (MILESTONES 1-2-14)
- **結晶製造機の定義** — 別タスク (MILESTONES 1-2-15)

---

## 10. 安定状態 (Settled State) と落下処理

### 10.1 安定状態の定義

**安定状態 (Settled State)** とは、シェイプ内の全ての有効な非空象限が接地している状態を指す。
すなわち、`FloatingPos` を満たす位置が存在しない状態である。

Lean での定義:

```lean
-- S2IL/Operations/Settled.lean
def IsSettled (s : Shape) : Prop :=
  ∀ p : QuarterPos, p ∈ QuarterPos.allValid s →
    ¬ (QuarterPos.getQuarter s p).isEmpty → IsGrounded s p

noncomputable def isSettled (s : Shape) : Bool := decide (IsSettled s)
```

空シェイプ、および単一レイヤのみのシェイプは自明に安定状態である。

### 10.2 ゲーム規定

ゲーム上、**ベルトで搬送されるシェイプおよび各加工装置の入出力は常に安定状態であることが保証されている**（[game-system-overview.md](game-system-overview.md) 参照）。

不安定状態は加工装置の **内部処理** においてのみ一時的に発生する:

| 内部処理 | 不安定状態が発生する場面 |
|---|---|
| **切断 (Cut)** | 切断により支えを失った象限が浮遊する |
| **積み重ね (Stack)** | 上側シェイプの一部が下側の空象限上に浮遊する |
| **ピン押し (PinPush)** | レイヤ上限超過による truncate 後に浮遊部分が生じる |

これらの内部処理では、最終出力前に必ず落下処理 (`Shape.gravity`) が適用され、安定状態に復帰する。

### 10.3 安定状態を保存する操作

以下の操作は安定状態のシェイプに適用しても安定状態を保つ:

| 操作 | 関数 | 安定状態保存の理由 |
|---|---|---|
| 着色 (Paint) | `Shape.paint` | 象限の有無を変えない |
| 結晶化 (Crystallize) | `Shape.crystallize` | 象限の有無を変えない |
| 回転 (Rotate) | `Shape.rotateCW` 等 | 構造クラスタの位置関係を保存 |
| 180° 回転 | `Shape.rotate180` | `IsSettled.rotate180` として証明済み |

### 10.4 落下処理の保証

落下処理 `Shape.gravity` の出力は常に安定状態である。本性質は `Shape.gravity.isSettled` として形式化する。
Wave Gravity では、`s.length` 回の `waveStep` 後に `FloatingPos` が存在しないことを示し、そこから `IsSettled` を導く。

---

## 11. Lean 実装状況

### 11.1 実装済みの定義

**`S2IL/Shape/Types.lean`**:

```lean
/-- 象限が構造結合を形成できるかを判定する。
    空とピン以外のシェイプ種別が結合能力を持つ -/
def Quarter.canFormBond : Quarter → Bool
    | empty       => false
    | pin         => false
    | crystal _   => true
    | colored _ _ => true
```

### 11.2 実装ファイル

**`S2IL/Operations/Settled.lean`**:

| 関数 | 役割 | 状態 |
|---|---|---|
| `IsContact` | 2象限間の接地接触 | ✅ 実装済み |
| `IsUpwardGroundingContact` | 上方向接地接触 | ✅ 実装済み |
| `IsStructurallyBonded` | 2象限間の構造結合 | ✅ 実装済み |
| `IsGroundingEdge` | 接地関係の合成エッジ | ✅ 実装済み |
| `IsGrounded` | 象限の接地判定 | ✅ 実装済み |
| `IsSettled` / `isSettled` | 安定状態の判定 | ✅ 実装済み |

**`S2IL/Operations/Gravity.lean`** (facade):

| 関数 | 役割 | 状態 |
|---|---|---|
| `Shape.gravity` | 落下処理の公開 API | ✅ Wave Gravity 実装済み |
| `Shape.gravity.isSettled` | 落下後の安定性 | ✅ theorem |
| `Shape.gravity.of_isSettled` | 安定入力の不動点性 | ✅ theorem |
| `Shape.gravity.rotateCW_comm` | CW 回転等変性 | ✅ theorem |
| `Shape.gravity.rotate180_comm` / `Shape.gravity.rotateCCW_comm` | CW からの系 | ✅ theorem |

Wave Gravity の `Defs` / `Behavior` / `Equivariance` / `Internal` 分割は `S2IL/Operations/Gravity/` に実装済み。公開 API は facade の `S2IL/Operations/Gravity.lean` から参照する。

---

## 12. 用語対応表

| 本仕様での用語 | game-system-overview.md での用語 | Lean コード上の対応 |
|---|---|---|
| 構造結合 (Structural Bond) | — | `IsStructurallyBonded` |
| 結合能力 (Bond Capability) | — | `Quarter.canFormBond` |
| 構造クラスタ (Structural Cluster) | — | `IsStructurallyBonded` の推移閉包として扱う |
| 接地接触 (Grounding Contact) | — | `IsContact` |
| 上方向接地接触 (Upward Grounding Contact) | — | `IsUpwardGroundingContact` |
| 接地エッジ (Grounding Edge) | — | `IsGroundingEdge` |
| 接地 (Grounded) | — | `IsGrounded` |
| 浮遊位置 (Floating Position) | — | `FloatingPos` |
| Wave tick | — | `Shape.waveStep` |
| 落下 (Falling / Gravity) | 落下 | `Shape.gravity` |
| 安定状態 (Settled State) | 安定状態 (Settled State) | `IsSettled`, `isSettled` |
| 結晶結合 (Crystal Bond) | — | `IsCrystalBonded` |
| 砕け散り (Shatter) | 砕け散り (Shatter) | `Shape.shatterOnFall` |
| 脆弱 (Fragile) | 脆弱 (Fragile) | `Quarter.isFragile` |
