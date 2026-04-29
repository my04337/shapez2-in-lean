# Gravity 証明計画（Phase D-10）

- 作成日: 2026-04-29
- 最終更新: 2026-04-29
- ステータス: **Phase D-10C 完了（`landingDistance_le_minLayer` 証明、`gravity.of_isSettled` を `IsNormalized` 仮定で theorem 化、ブリッジ axiom 1 本に集約。D-10D 着手可）**
- スコープ: `S2IL/Operations/Gravity.lean` の脱 axiom（Phase D 最終 4 axiom）
- 上位計画: [layer-ab-rewrite-plan.md §4.3](layer-ab-rewrite-plan.md)
- 構造拘束: [architecture-layer-ab.md §1.4.4](architecture-layer-ab.md)
- 仕様: [docs/shapez2/falling.md](../shapez2/falling.md)

---

## 0. この計画書の位置付け

Gravity（落下機構）は Layer B で唯一残る重実装ノードであり、過去に複数回の証明破綻を起こしている（[`/memories/repo/waveStep-grounding-mono-persistence.md`](#)）。本書は **着手前に必要な事前検証** と **証明全体の地図** を提供し、
過去の失敗パスを反復しないことを目的とする。

実施手順（具体的な補題着手順や PR 単位）は本書 §6 / §7 を参照。各 sorry の作業ノートは
`S2IL/_agent/sorry-cards/` に分割記録する。

---

## 1. 仕様の再確認（インテント固定）

[docs/shapez2/falling.md](../shapez2/falling.md) §6 の **1 パスアルゴリズム** を採用する:

1. 入力 `s` から構造クラスタと孤立ピンを算出（**開始時点に確定**、以降不変 = 結合凍結）
2. 接地判定で落下単位（浮遊クラスタ + 浮遊ピン）を列挙
3. 落下単位を `shouldProcessBefore` で部分整列（同一方角列で下位を先）
4. 障害物シェイプ `O` を「全落下単位を除去した `s`」で初期化
5. 各落下単位 `U` を順に処理: 着地距離 `d(U)` を決め、`O` を更新
6. 最終結果を normalize

### 1.1 結合凍結（Bond Freezing）の必須性

> **重要**: 落下中に「現在の」grounding を再計算すると仕様と乖離する。

**反例（§6.5 例 5）**:

入力 `Cr------:RgRg----:----Sb--`。Sb は L2:SW にあり、L1:SW が空のため非接地。
仕様の出力は `Cr--Sb--:RgRg----`（Sb は layer 0 まで落下）。

**Naive な「1 ステップずつ全 non-grounded を 1 段下ろす」アルゴリズムの反例**:

```
Step 1: --Sb-- が (2,SW)→(1,SW) に降下 → Cr------:RgRgSb--:--------
Step 2: ここで grounding を再計算すると、L1:SE(Rg) と L1:SW(Sb) が水平接地接触
        （両者非ピン）→ Sb は接地と判定 → 停止
結果: Cr------:RgRgSb--（仕様と異なる）
```

このため、**落下単位の同一性は開始時に固定** し、各単位は自身の cluster ID を保持して
独立に落下する必要がある。これが `IsBonded` / `IsGrounded` の 1 回計算と、
「単位 → 落下距離」の 1 回写像で表現される所以。

### 1.2 採用する数学モデル

落下処理 `gravity : Shape → Shape` を、次の 4 性質を満たす **唯一の関数** として規定する
（[architecture §1.4.4](architecture-layer-ab.md) の図解参照）:

| 性質 | 命題 |
|---|---|
| 全関数性 | `gravity : Shape → Shape`（0 層入力 → 0 層出力。§1.9 Option 追放原則）|
| 安定性 | `IsSettled (gravity s)` |
| 不動点性 | `IsSettled s ∧ IsNormalized s → gravity s = s` （※D-10C 確定形。§1.2.1 参照） |
| CW 等変性 | `(gravity s).rotateCW = gravity s.rotateCW` |
| 180° / CCW 等変性 | CW の 1 行系（§1.4 単一チェーン原則） |

#### 1.2.1 `IsNormalized` 追加仮定の根拠（D-10C 確定）

当初は `IsSettled s → gravity s = s` だったが、次の反例を持つ:

```
s = [L_grounded, L_empty]   -- L_grounded は L0 で接地済み、L_empty は末尾の空レイヤ
IsSettled s     ✓ (allValid s 上の非空象限は全て grounded、空レイヤは vacuous)
gravity s = [L_grounded]     -- 末尾の `Shape.normalize` で L_empty が除去される
s ≠ gravity s
```

spec [`falling.md §6.6`](../shapez2/falling.md) は **出力が常に正規形** と規定するため、`gravity` は末尾空レイヤを除去する `normalize` を必須とする。一方 `IsSettled` は接地条件のみを規定し、レイヤ構造の正規性は要求しない。両者を整合させるには `IsNormalized s` を入力にも仮定するのが自然である（shape の構造的不変は spec 上は常に正規形だが、Lean では `Shape := List Layer` の abbrev で型強制を避けたため API 仮定で扱う）。

これらが Layer C / Machine から要求される全 API である。冪等性（§7.3）/ レイヤ数不増（§7.4）は
派生定理として facade に追加するが、必須ではない。

---

## 2. 過去の失敗パスと教訓

### 2.1 旧 Wave Gravity モデル（`_archive/pre-greenfield/Operations/Gravity/`）の構造

旧実装は次の階層で構成されていた:

```
processWave : Shape → Shape    -- 1 wave = 最下位 minLayer 群を一括着地
process s := iterate processWave until floatingUnits = []
gravity s := process s.normalize
```

各 wave で:
1. `floatingUnits s` を算出（List FallingUnit）
2. `minLayer` 最小の wave を `settling` として filter
3. `settling` を `landingDistance` 昇順に mergeSort
4. `placeLDGroups`: 障害物シェイプを単位ごとに更新しながら fold で書き込む

### 2.2 主な破綻ポイント

| 課題 | 旧補題名 | 失敗内容 |
|---|---|---|
| 群間の書き込み持続 | `placeLDGroups_landing_groundingEdge_mono` | group j の cluster 着地が group k > j の pin 着地で上書きされる場合の groundingEdge 単調性が閉じない |
| 終端性 | `waveStep_ngs_strict_bound` | 上記 mono に依存。NGS 厳密減少が `_archive` 末まで sorry |
| 重複等変性チェーン | `process_rotate180` / `processWave_rotateCW_comm` 等 | 各 BFS / fold 段で個別の `rotate180_comm` / `rotateCW_comm` 補題を定義し連鎖（数十本） |

### 2.3 抽出された教訓

1. **意味論層と実装層の分離不足**: 旧モデルは `processWave` の代数的性質と `placeLDGroups` の実装を同一層で扱い、補題が爆発した。
2. **障害物シェイプの逐次更新**: `obs_k` が group 処理ごとに変わるため、各群の不変条件を「全群を通じて」述べるのが極めて重い。
3. **List 順序依存**: `mergeSort` / `Sort` の証明では `List.Perm` 経由で常に等変性を持ち上げる必要があり、補題が冗長化。
4. **インデックス到達補題が分散**: `groundedPositions_mono_of_edge` が Settled 層と Gravity 層で重複定義（循環依存回避のため）。

### 2.4 再利用可能な資産（[layer-ab-rewrite-plan.md §7](layer-ab-rewrite-plan.md) Step 1/2 で再評価）

| 旧補題 | 評価 | 処置 |
|---|---|---|
| `IsBonded` / `ClusterRel` の関係層 | ✅ 数学的に美しい | Phase C で既に再構築済み（`Kernel/Cluster.lean`） |
| `IsGrounded` / `IsSettled` (`Relation.ReflTransGen`) | ✅ 美しい | Phase D-1 で再構築済み（`Operations/Settled.lean`） |
| `nonGroundedLayerSum` / `ngsWeight` | △ 算法依存 | 新モデルでは終端性が単純化されるため不要の可能性。必要時のみ移植 |
| `floatingUnits` / `FallingUnit` 構造 | ○ 概念は保持 | List ではなく **Finset (Finset QuarterPos) ⊕ Finset QuarterPos** で再表現 |
| `landingDistance` | ○ 概念は保持 | declarative 化（Prop 述語の `Nat.find` で定義） |
| `placeLDGroups` / `placeQuarter` / `setDir` の fold チェーン | ✗ 廃棄 | 障害物逐次更新を避ける新表現に置換 |
| `process_rotate180` / `process_rotateCW_comm` の証明テンプレート | △ アイデア参考 | 補題本体は再実装。`ClusterRel.rotateCW` / `IsGrounded.rotateCW` を直接使う |

---

## 3. 候補アプローチの評価

### 3.1 候補一覧

| 案 | 概要 | 計算可能性 | 主リスク |
|---|---|---|---|
| (a) `gravityStep` の有限反復 | 1 段ずつ落下、NGS 厳密減少で終端 | `decide` 可（grounding が `noncomputable` なので実質 noncomputable） | 結合凍結を素朴に表現できず、§6.5 例 5 で仕様乖離 |
| (b) `IsSettled` 判定 + `Classical.choose` | 「設定された結果」の述語の唯一存在から取得 | 不可（fully noncomputable） | 存在 + 一意性証明が algorithmic な内容を要求 |
| (c) LDGroup 一発配置（旧 wave モデル） | 既存資産の移植 | 部分的 | `placeLDGroups_landing_groundingEdge_mono` の再演リスク |
| **(d) 宣言的仕様 + minimum displacement の Nat.find** | 落下単位ごとに最大降下距離を `Nat.find` で取得し配置 | noncomputable（`IsGrounded` 経由で `decide` 可だが Classical 必要） | 個別 `Nat.find` の存在と「最大性」の単調性証明 |

### 3.2 (a) 単純反復は仕様乖離（§1.1 で実証）

→ **不採用**。

### 3.3 (b) 完全宣言的は存在証明が algorithmic

存在証明を書こうとすると結局 (c) または (d) に帰着する。形式上は美しいが「中身を書かないと閉じない」ため、表面的な美しさに留まる。

→ 単独では **不採用**。ただし最終的な公開 API シグネチャは (b) 風に整える（`gravity := Classical.choose ...` ではなく具体 `def`、`gravity_spec` で述語との同値性を別途与える）。

### 3.4 (c) 旧 wave モデル移植

過去の失敗パスを再演するリスクが極めて高い。group 間 `obs_k` の干渉という根本問題が残ったまま。

→ **不採用**。

### 3.5 採用案: **(d) 落下単位ごとの最大降下距離を宣言的に定める**

**コア概念**:

各落下単位 `U` ⊂ `QuarterPos` に対し、**降下距離 `dropOf U s : Nat`** を次の述語で唯一に定める:

```
CanDropBy s U d : Prop ↔
  -- U を d 段下ろした位置 {(p.layer - d, p.dir) | p ∈ U} が
  -- 1. すべて layer ≥ 0（= d ≤ U.minLayer）
  -- 2. もとのシェイプの非落下位置（= s minus all falling units）と衝突しない
  -- 3. ほかの落下単位（= 自身より小さい dropOf を持つもの）の着地後とも衝突しない
```

`dropOf U s := Nat.find (CanDropBy s U) over { d | CanDropBy s U d }`、ただし「他の落下単位の着地」は `dropOf` 自身を再帰的に参照する。これを well-founded 再帰で定義する（measure: `U.minLayer`）。

**処理順序の決定性**:

`shouldProcessBefore` は **同一方角列内で minLayer の小さい単位を先に処理する** という制約のみを記述する半順序。これは `dropOf` の well-founded 再帰の measure に直接対応する:

```
dropOf U s := 
  let lowerUnits := { U' : FallingUnit | U' ≠ U ∧ shareDirection U U' ∧ U'.minLayer < U.minLayer }
  let lowerLandings := lowerUnits.image (fun U' => (U', dropOf U' s))   -- 再帰
  computeMaxDrop U s lowerLandings
```

`shareDirection` を共有しない単位は互いの着地位置に影響しないため（[falling.md §6.4](../shapez2/falling.md)）、再帰は半順序で well-founded。

**主要利点**:

1. **障害物シェイプの逐次更新を避ける**: `dropOf U` は他の単位の `dropOf` のみに依存し、`obs_k` のような中間状態を持たない
2. **結合凍結が自然**: 落下単位の集合は `s` から 1 回のみ計算（`Operations.Settled` の `IsGrounded` 経由）
3. **等変性が単純**: `dropOf U s = dropOf U.rotateCW s.rotateCW`（CW で `minLayer` 不変、`shareDirection` 不変、衝突判定不変）
4. **不動点性が自明**: `IsSettled s` なら落下単位 0 個 → `gravity s = s`（fold over ∅）
5. **終端性が自明**: `dropOf U` が well-founded 再帰、`gravity` 自体は単一 fold

**残るリスク**:

- `dropOf` の well-founded 再帰（Lean では `decreasing_by`）が `shareDirection` の同値類で崩れないかの確認
- 衝突判定 `CanDropBy s U d` の正確な定式化（pin / cluster 混在時）
- 等変性の詳細（`shareDirection.rotateCW` / `CanDropBy.rotateCW`）

これらは個別補題として §6 で具体化する。

---

## 4. 反例検証先行（着手 GO 条件 §1.5）

着手前に以下を `lean-counterexample` / `#eval` で検証する。すべて成功してから §6 着手。

### 4.1 `gravity` の期待出力テスト

| 入力（vanilla4） | 期待出力 | 仕様参照 |
|---|---|---|
| `Cr------:--Cr----` | `CrCr----` | §6.5 例 1 変形 |
| `--------:--Cr--Cr` | `--Cr--Cr` | §6.5 例 2 |
| `CrCr----:----RgRg` | `CrCrRgRg` | §6.5 例 3 |
| `CrCr----:--RgRg--` | `CrCr----:--RgRg--`（不変） | §6.5 例 4 |
| `Cr------:RgRg----:----Sb--` | `Cr--Sb--:RgRg----` | §6.5 例 5（結合凍結） |
| `--------:P-------:Cr------` | `P-------:Cr------` | §6.5 例 6 |
| `CrCrCrCr:P-------:RgRgRgRg` | `CrCrCrCr:P-------:RgRgRgRg`（不変） | §6.5 例 7 |
| `--CrCr--:--------:--RgRg--` | `--CrCr--:--RgRg--` | §6.5 例 8 |
| `CrCr----:--------:--RgRg--:--------:----SbSb` | `CrCr----:--RgRg--:----SbSb` | §6.5 例 9（下位優先） |

**検証手順**: REPL で各入力に対し `gravity` 仕様の手計算結果を `#guard` テストとして書き、新実装で `decide`（`Classical` 経由）または `#eval` で確認する。

#### 4.1.1 噛み合い（interlock）パターン — stress8 想定

旧 foldl モデル（1 ステップずつ全非接地単位を 1 段降下）が **6 層超で破綻した代表的シナリオ** を、§3.5 (d) の宣言的モデルが正しく扱えるかを確認するためのケース群。
共通する構造:

- 落下単位 A・B が互いに **同一方角列を共有** し、片方の単位が他方の「内側」「鈎」「歯」に入り込む幾何
- A 単独で 1 段降下しようとすると B の象限と衝突、B 単独で降下しようとすると A の象限と衝突する
- 仕様の 1 パス処理（[falling.md §6](../shapez2/falling.md)）では下位優先ソート + 障害物シェイプの逐次更新で**順序づけて確定**する

> **クラスタ間の結合回避**: 通常の象限同士は隣接で結合するため、2 つの落下クラスタを「同じ方角列で噛み合わせる」と必ず結合してしまう。本節のパターンは **ピン（`P`）** または **空レイヤ挟み込み** で結合を切り、独立した 2 単位として interlock を成立させる。

##### I-1: 凹型クラスタ ＋ 内部ピン（5 層、最小 interlock）

```
入力: --------:--------:CrCr----:P-Cr----:CrCr----
```

レイヤ構造（NE/SE/SW/NW 順、L0 が最下層）:

| レイヤ | NE | SE | SW | NW | 注 |
|---|---|---|---|---|---|
| L4 | Cr | Cr | – | – | 凹 A の上腕 |
| L3 | **P** | Cr | – | – | A の SE 桁 + 内部ピン α |
| L2 | Cr | Cr | – | – | A の下腕 |
| L1 | – | – | – | – | 浮遊 |
| L0 | – | – | – | – | 空 |

- クラスタ A = `{NE(2), SE(2), SE(3), SE(4), NE(4)}`（SE 列で連結。NE(3) はピンで結合断）
- ピン α = `NE(3)`（A の depression に居る）
- A・α とも非接地（L1 が空）

**期待出力**: `CrCr----:P-Cr----:CrCr----`（A が 2 段降下、α が同行して NE(1) に着地、3 層に圧縮）

**foldl モデルの破綻点**: 1 段降下を再帰的に試すと、α が NE(2) を通過する際に「A の元 NE(2) に乗る」と誤認し終端判定が誤る。仕様 1 パスでは α の処理時に O = A の新位置となり、α は NE(1) で正しく着地する。

##### I-1': 口型クラスタ + 内部単一象限クラスタ（8 層、ピン以外の異形質含有）

I-1 はピン α が depression に入る形だが、本ケースは **別形質の単一象限クラスタ** が口型クラスタの中央に挟まる。
ピンは `canFormBond = false` で初めから結合断するが、こちらは両者とも `canFormBond = true` でありながら **隣接位置に来ない幾何配置** によってのみ結合が断たれる、という質的に異なる落下処理経路を踏む。

```
入力:  --------:--------:CrCrCr--:Cr------:Cr--Rg--:Cr------:CrCrCr--:--------
出力:  CrCrCr--:Cr--Rg--:Cr------:Cr------:CrCrCr--
```

レイヤ構造（L0 が最下層）:

| レイヤ | NE | SE | SW | NW | 注 |
|---|---|---|---|---|---|
| L7 | – | – | – | – | 末尾空（normalize で除去） |
| L6 | Cr | Cr | Cr | – | 口 A の上辺（NE-SE-SW 連結） |
| L5 | Cr | – | – | – | A の NE 桁 |
| L4 | Cr | – | **Rg** | – | A の NE 桁 + 内部単一クラスタ B |
| L3 | Cr | – | – | – | A の NE 桁 |
| L2 | Cr | Cr | Cr | – | 口 A の下辺 |
| L1 | – | – | – | – | 浮遊 |
| L0 | – | – | – | – | 空 |

- クラスタ A（Cr, 9 象限）: NE 列 L2-L6 と L2:SE,SW・L6:SE,SW を SE 列・水平接触で連結した 口
- クラスタ B（Rg, 1 象限）: `(layer=4, dir=SW)` 単独。隣接 4 位置は L4:SE(空), L4:NW(空), L3:SW(空), L5:SW(空) のため A と非結合
- 両者非接地（L1 全空）。落下単位 = {A, B}

**期待される処理**:

| Step | unit | minLayer | dropOf | 着地後の位置 |
|---|---|---|---|---|
| 1 | A | 2 | 2 | NE: L0-L4, L0:SE,SW, L4:SE,SW |
| 2 | B | 4 | 3 | L1:SW（直下 L0:SW が A 着地後 Cr） |

→ 出力 5 層: L0 `CrCrCr--`, L1 `Cr--Rg--`, L2 `Cr------`, L3 `Cr------`, L4 `CrCrCr--`。✓

**foldl モデル特有の破綻点（ピン版とは別経路）**: B も `canFormBond = true` のため、1 ステップずつ降ろす過程で B が **A の側壁** に接近すると "結合候補位置" として追跡されてしまう。仕様の §6.1 結合凍結原則では落下中に新規結合は形成されないため、B は最後まで独立単位として扱われ A 着地後の障害物のみで停止する。foldl + 各 step での結合再評価は、この凍結原則に反するため 6 層超で **B の所属クラスタが途中で A に合流したと誤認** → 落下停止位置がずれる。

> **位置付け**: 本ケースは I-1 のピン版と並行して `#guard` 凍結する。両者の `dropOf` 計算経路が同一で、結合判定の側だけが異なることを実装で担保する（`FallingUnit.cluster` と `FallingUnit.pin` の処理を統一できる根拠）。

##### I-2: 凹×凹 縦二段スタック（8 層、stress8 主反例）

```
入力: --------:RgRg----:P-Rg----:RgRg----:--------:CrCr----:P-Cr----:CrCr----
```

| レイヤ | NE | SE |
|---|---|---|
| L7 | Cr | Cr |
| L6 | **P** | Cr |
| L5 | Cr | Cr |
| L4 | – | – | （A・B 分離用の空レイヤ）
| L3 | Rg | Rg |
| L2 | **P** | Rg |
| L1 | Rg | Rg |
| L0 | – | – |

- 落下単位 4 個: クラスタ A（Rg, L1-L3）、ピン α（NE(2)）、クラスタ B（Cr, L5-L7）、ピン β（NE(6)）
- 全単位が浮遊。L4 が空のため A と B は結合しない
- 各 凹 クラスタの depression に 1 つずつピンが入っている **二段噛み合い**

**期待出力**: `RgRg----:P-Rg----:RgRg----:CrCr----:P-Cr----:CrCr----`（全単位がそのままの相対形状で 6 層に圧縮、A は 1 段、α は 1 段、B は 2 段、β は 2 段降下）

**foldl モデルの破綻点**: 1 ステップ後に B が「α の上に着地した A」を再計算で接地と誤判定し、B の着地点を 1 段ずれて確定してしまう。再計算ループの停止条件が単純な「全非接地 = 0」だと B のずれが解消されないまま終端する。**6 層を超えて段が増えるほど誤差が累積する**のが旧 wave モデル破綻の核心。

##### I-3: `waveStep_grounding_mono_persistence` 破綻型（Phase D-10A 後に確定）

旧 wave モデルで破綻した「群間着地スロットの上書き干渉」（[memo](#)）を **採用モデル (d) では発生させない** ことを示す主反例。
具体的には:

- 落下単位 A（cluster, minLayer=`m_A`）と落下単位 B（pin or cluster, minLayer=`m_B`）が同一方角列を共有
- `m_A < m_B` で処理順は A → B
- A の `dropOf = d_A` 着地後、B が `dropOf = d_B` で「A の着地スロット直上」に着地する
- 旧モデルでは B の着地書込が A の着地書込を **上書き** し、A 側の `canFormBond` 象限が pin に置換されて `IsGrounded` 持続性が崩れた
- 採用モデル (d) では、A・B の `dropOf` を 1 回計算した固定写像とし、`CanDropBy` の衝突判定で「同一スロットへの 2 単位着地」を構造的に排除する

**現状**: 上記を満たす **最小幾何の入力シェイプ** は、採用モデル (d) の `CanDropBy` / `dropOf` の Lean 定義（Phase D-10B 完了時点）で確定する `衝突` 述語の正確な形に依存する。
Phase D-10A 着手時点では空欄とし、Phase D-10B（`Defs.lean` / `Internal/Drop.lean` 完成）後に REPL で:

```
#eval Operations.Gravity.gravity (testInput.toShape)
#guard Operations.Gravity.gravity (testInput.toShape) = expectedOutput
```

を実行して凍結する。本反例は **Phase D-10D 安定性主定理の前提** として §9 の GO 条件に追加する。

> 旧モデルの破綻は「同列の cluster と pin が異なる drop 距離で着地スロットが重なる」ことに起因していた。採用モデル (d) は cluster/pin を **同一の `FallingUnit.positions` Finset** として扱うため、衝突判定が一様化され、上書きが発生しない構造になっている。この性質の検証が I-3 の役割。

### 4.2 `gravity_isSettled` の反例検索

`lean-counterexample` で `∀ s, IsSettled (gravity s)` を `vanilla4` / `vanilla5` 全 Shape 列挙で検証する（noncomputable のため `decide` を `Classical` で起動）。

> **注意**: `IsSettled` の Decidable インスタンスは `Classical.decPred` 経由で `noncomputable` のため、`plausible` から駆動すると 1 件ごとに classical decide が走り実用速度に至らない。Phase D-10B で executable な `Shape.isSettledFast : Shape → Bool` を導入した後は `plausible` でランダム検証が可能になる（§4.4 参照）。

### 4.3 `gravity_rotateCW_comm` の反例検索

`∀ s, (gravity s).rotateCW = gravity s.rotateCW` を `vanilla4` 全 Shape で検証する。

---

### 4.4 Plausible 適用方針（Phase D-10B 以降）

`Shape.gravity` は axiom のため Phase D-10A では plausible 検証不可。D-10B で executable な実装が入った時点で以下をプロパティ化する:

```lean
-- 安定性（isSettledFast は Phase D-10B で導入する executable Bool 版）
example : ∀ (s : Shape), Shape.isSettledFast (Shape.gravity s) = true := by plausible

-- 不動点性
example : ∀ (s : Shape), Shape.isSettledFast s = true → Shape.gravity s = s := by plausible

-- CW 等変性
example : ∀ (s : Shape), (Shape.gravity s).rotateCW = Shape.gravity s.rotateCW := by plausible

-- レイヤ数不増
example : ∀ (s : Shape), (Shape.gravity s).layers.length ≤ s.layers.length := by plausible

-- 冪等性
example : ∀ (s : Shape), Shape.gravity (Shape.gravity s) = Shape.gravity s := by plausible
```

各プロパティは **vanilla4 → vanilla5 → stress8** の順で `SampleableExt Shape` を切り替えて検証する。
vanilla5 / stress8 用には `Arbitrary.lean` の `shapeGen`（0..4 layers）を局所上書きするジェネレータが必要。

**試行回数指針**（[`/memories/repo/counterexample-layer-benchmark.md`](/memories/repo/counterexample-layer-benchmark.md) 由来）:

| 範囲 | 推奨試行回数 | 理由 |
|---|---|---|
| vanilla4 (0..4 layers) | 100（既定） | パターン空間 ~6,500、既定で十分 |
| vanilla5 (0..5 layers) | 1,000 | 空間 ~60,000、ランダムで要所カバー |
| stress8 (6..8 layers) | 500–1,000 | 空間爆発のためランダム必須 |

`#guard` ベースの代表値テストは別途 `Test/Operations/Gravity.lean` に置く（plausible はあくまで補助）。

### 4.5 Phase D-10A 設計観点チェックリスト

§4.1 / §4.1.1 の手計算トレースから抽出した、採用モデル (d) が **必ず保たなければならない構造前提** 7 項目。
Phase D-10B 以降の `#eval` / plausible が反例を返した場合は、**反例最小化後にどれが破綻しているかを特定する**。

1. **落下単位凍結（Bond Freezing）**: `floatingUnits` は入力 `s` から 1 回だけ計算し以降再評価しない。例 5 で Sb が L2:Rg と隣接通過しても結合しないことを保証。
2. **障害物シェイプの構築**: O = 「全落下単位の**元位置**を除去した残余」+「先行 unit の**新位置**」。元位置を残すと例 9 で C が B の元位置を障害物と誤認する。
3. **衝突判定の統一**: cluster と pin の `dropOf` 計算を `FallingUnit.positions : Finset QuarterPos` に正規化し **同一の衝突述語** で扱う（I-1 ピン α と I-1' 単一象限クラスタ B が同じ計算経路を踏む根拠）。
4. **shouldProcessBefore の最小性**: 「方角列共有 ∧ minLayer 厳密小」のみで処理順を一意化。I-2 の A→α→B→β 順序決定に追加 tie-break 不要。
5. **同列非共有 unit の独立性**: 方角列を共有しない unit は互いの dropOf に影響しない。`floatingUnits` を `Finset` で扱える根拠。
6. **層 0 到達優先**: 着地条件 ①（`q.layer - d = 0`）は ②（障害物直下非空）より優先。例 1 で空 O 上の落下が layer 0 で停止する。
7. **正規化は fold 後に 1 回**: 中間 `normalize` 呼出しで `dropOf` の layer インデックスが崩れる。

#### 反例発覚時のモデル再設計チェックリスト（R-A〜R-E）

万一 Phase D-10B 以降で plausible が反例を出し採用モデル (d) が破綻した場合:

- **R-A**: plausible の shrink 出力で **layerCount / 落下単位数 / pin 含有有無** の最小条件を確定し、上記 1〜7 のどれが破綻しているかを特定
- **R-B**: spec [falling.md §6.5](../shapez2/falling.md) の 9 例 + interlock I-1/I-1'/I-2 が引き続き成立することを再トレース
- **R-C**: 旧 wave モデルの破綻パス（[`/memories/repo/waveStep-grounding-mono-persistence.md`](/memories/repo/waveStep-grounding-mono-persistence.md)）の再現条件を新モデルでチェック
- **R-D**: §3.5 (b) 完全宣言的（`Classical.choose` + 一意性証明）への pivot を検討
- **R-E**: §3 候補 (a)〜(d) を再評価し、破綻した構造前提を回避する新案を策定

---

## 5. ファイル構成

[architecture-layer-ab.md §1.3 / §2](architecture-layer-ab.md) に従う MECE 分割:

```
S2IL/Operations/Gravity.lean              # facade（公開 API、≤ 150 行）
S2IL/Operations/Gravity/
├── Defs.lean                             # FallingUnit / floatingUnits / dropOf / gravity（≤ 300 行）
├── Behavior.lean                         # IsSettled / 不動点 / 単調性（≤ 300 行）
├── Equivariance.lean                     # CW 等変性主証明（≤ 300 行）
└── Internal/
    ├── Drop.lean                         # CanDropBy 述語と Nat.find 抽出（≤ 300 行）
    ├── ShareDirection.lean               # 落下単位の方角共有関係と well-founded（≤ 300 行）
    └── Collision.lean                    # 衝突判定とその CW 等変性（≤ 300 行）
```

`Internal/` は `Gravity.lean` および `Gravity/*.lean` からのみ import。`Test/Behavior/Gravity.lean` は §4 の例を `#guard` テスト化。

---

## 6. 補題チェーン（MECE）

### 6.1 Layer A 部（純粋関数定義）— `Defs.lean`

| 補題/定義 | 内容 | 依存 |
|---|---|---|
| `FallingUnit` | `inductive FallingUnit \| cluster (ps : Finset QuarterPos) \| pin (p : QuarterPos)` | — |
| `FallingUnit.positions` | unit に含まれる位置（Finset） | — |
| `FallingUnit.minLayer` | 最小レイヤ | — |
| `floatingClusters s : Finset (Finset QuarterPos)` | 浮遊クラスタの集合（`clusterSet` から非接地のもの） | Settled, Cluster |
| `floatingPins s : Finset QuarterPos` | 浮遊ピン位置 | Settled |
| `floatingUnits s : Finset FallingUnit` | 上 2 つの和 | — |
| `shareDirection (U V : FallingUnit) : Bool` | U と V が方角列を共有するか | — |
| `CanDropBy s U d : Prop` | U を d 段下ろした結果が `s` 内および下位 unit の着地後と衝突しないか | Settled |
| `dropOf s U : Nat` | well-founded 再帰で `Nat.find (CanDropBy s U)` を最大化 | — |
| `gravity s : Shape` | 全落下単位を `dropOf` ぶん下ろして `normalize` | — |

### 6.2 Layer B 部（振る舞い系）— `Behavior.lean`

| 定理 | 内容 | 主依存 |
|---|---|---|
| `dropOf_le_minLayer` (= `landingDistance_le_minLayer`) | `landingDistance obs u ≤ u.minLayer`（layer 0 を割らない）| Drop.lean |
| `gravity.isSettled` | `IsSettled (gravity s)` | dropOf 構造、Collision |
| `gravity.of_isSettled` | `IsSettled s ∧ IsNormalized s → gravity s = s`（D-10C 確定形、§1.2.1）| floatingUnits = ∅ + IsNormalized |
| `gravity.idempotent` | `gravity (gravity s) = gravity s`（系） | 上 2 本 |
| `gravity.layerCount_le` | `(gravity s).layerCount ≤ s.layerCount` | normalize の性質 |

### 6.3 Equivariance 部 — `Equivariance.lean`

| 定理 | 内容 | 主依存 |
|---|---|---|
| `floatingUnits.rotateCW_comm` | `floatingUnits s.rotateCW = (floatingUnits s).image FallingUnit.rotateCW` | `IsGrounded.rotateCW`, `clusterSet.rotateCW_comm` |
| `shareDirection.rotateCW` | `shareDirection U.rotateCW V.rotateCW = shareDirection U V` | minLayer / column の rotateCW 不変 |
| `CanDropBy.rotateCW` | `CanDropBy s.rotateCW U.rotateCW d ↔ CanDropBy s U d` | Collision |
| `dropOf.rotateCW` | `dropOf s.rotateCW U.rotateCW = dropOf s U` | 上 3 本 |
| **`gravity.rotateCW_comm`** | `(gravity s).rotateCW = gravity s.rotateCW` | dropOf.rotateCW |
| `gravity.rotate180_comm` | facade 1 行系（§1.4） | CW |
| `gravity.rotateCCW_comm` | facade 1 行系（§1.4） | CW |

### 6.4 Internal 補題

#### `Internal/ShareDirection.lean`

- `shareDirection.symm`
- `shareDirection_iff_mem_columns`（共有方角集合の特徴付け）
- well-founded 関係 `(<U V) := shareDirection U V ∧ U.minLayer < V.minLayer` の `WellFoundedRelation` instance

#### `Internal/Drop.lean`

- `CanDropBy_zero` (`CanDropBy s U 0`)
- `CanDropBy_antitone` (`CanDropBy s U (d+1) → CanDropBy s U d`)
- `CanDropBy_bounded` (`CanDropBy s U d → d ≤ U.minLayer`)
- `dropOf_eq_findGreatest` (Mathlib `Nat.findGreatest` 経由で抽出)

#### `Internal/Collision.lean`

- 衝突判定の primitive（pin / cluster 混在時の場合分け）
- `Collision.rotateCW`

---

## 7. 段階的着手手順（Phase D-10A → D-10E）

各段階は独立にコミット可能、`lake build` green を維持。失敗時は `lean-proof-progress` の撤退判断（3 セッション or 8 アプローチ）で次段階に進まず本書の §3.5 (d) 設計を再評価する。

### Phase D-10A: 反例検証先行（GO 条件確認）— **完了 2026-04-29**

§4 の検証を完了。結果:

- §4.1 の 9 例（例 1〜例 9）: spec [falling.md §6.2](../shapez2/falling.md) のアルゴリズムに対する手計算トレースで **すべて期待出力と完全一致**（反例なし）
- §4.1.1 interlock パターン I-1（凹+ピン 5 層）/ I-1'（口型+単一象限 8 層）/ I-2（凹×凹 縦二段 8 層）: **すべて整合**（採用モデル (d) が正しく処理可能）
- I-3: `CanDropBy` 形状確定後（D-10B 完了時点）に持ち越し。これは設計上の意図的な持ち越し
- Plausible 適用範囲: `gravity` 自体は axiom のため Phase D-10A では適用不可。基本 S2IL 型に対する plausible 動作は確認済み（[`Scratch/PhaseD10A_Plausible_v2.lean`](../../Scratch/PhaseD10A_Plausible_v2.lean) で 3 件パス）
- 設計観点 7 項目 + 再設計時チェック観点 5 項目を [docs/lean/plausible-guide.md](../lean/plausible-guide.md) に反映済み

**GO 判定**: D-10B 着手可能。

### Phase D-10B: Layer A 部 — 1〜2 セッション想定 — **完了 2026-04-29**

`Defs.lean` の定義群と `Internal/ShareDirection.lean` の well-founded 関係を実装。
`#eval gravity (...)` で §4.1 の代表例が一致することを確認。

**実装結果**:

- [`S2IL/Operations/Gravity/Defs.lean`](../../S2IL/Operations/Gravity/Defs.lean): 計算可能な Layer A 定義群（`structuralNeighbors` / `structuralCluster` / `floatingUnits` / `landingDistance` / `Shape.gravity`）。`Shape.gravity` は axiom から `def` に格上げ。
- [`S2IL/Operations/Gravity/Internal/ShareDirection.lean`](../../S2IL/Operations/Gravity/Internal/ShareDirection.lean): `shareDirection.symm` 証明 + `precedes` の well-founded 関係（`Nat.strong_induction_on` on `minLayer`）。
- [`S2IL/Operations/Gravity.lean`](../../S2IL/Operations/Gravity.lean): facade 更新、axiom は 4→3（`isSettled` / `of_isSettled` / `rotateCW_comm`、`gravity` 自体は def 化）。
- 検証: [`Scratch/PhaseD10B_GravityCheck.lean`](../../Scratch/PhaseD10B_GravityCheck.lean) — §4.1 の 9 例 + §4.1.1 I-1（5 層、結晶版）+ I-2（凹×凹 縦二段、8 層）= 計 11 件すべて `#guard` パス。レイヤ数不増 4 件 + 冪等性 6 件もパス。
- Plausible: [`Scratch/PhaseD10B_GravityPlausible.lean`](../../Scratch/PhaseD10B_GravityPlausible.lean) — `layerCount` 単調減少 + 冪等性（toString レベル）を Plausible 100 件で `Unable to find a counter-example`。

**設計上の修正（重要）**: §3.5 / §6.1 当初記述の `clusterSet`（`Kernel.IsBonded` 経由 = 結晶結合のみ）は、仕様 [falling.md §2.2](../shapez2/falling.md) の **構造結合**（`Quarter.canFormBond` で「非ピンかつ非空の隣接」を許容）と異なる。実装では構造結合を採用し、新規述語 `structuralNeighbors` / `structuralCluster` として導入した。結晶結合は shatter のみで使用する。

**着地距離の修正**: 当初の「最大の有効 d（着地点が空のまま降下できる最大量）」は仕様 [§6.3](../shapez2/falling.md) の落下物理と不一致。実装では「**最小の d ≥ 1** で『床到達 (q.1 = d)』または『直下に障害物』のいずれかが成立する d」（`landingDistance`）を採用。`#eval` 全例で仕様一致を確認。

**GO 判定**: D-10C 着手可能。`gravity` は def なので `#eval gravity s = ...` 形式の振る舞い検証は今後 Layer B 補題証明中に随時 REPL で確認できる。

### Phase D-10C: 不動点・終端性 — **完了 2026-04-29**

[`Behavior.lean`](../../S2IL/Operations/Gravity/Behavior.lean) を新設し、不動点性と着地距離境界を確定形に整備。

**実装結果**:

- [`S2IL/Operations/Gravity/Behavior.lean`](../../S2IL/Operations/Gravity/Behavior.lean):
  - `Gravity.landingDistance_le_minLayer (obs u) : landingDistance obs u ≤ u.minLayer` — 直接証明（axiom-free）。`find?` の戻り値は元 list の要素であり、`range (m+1)` メンバーシップから `≤ m` を得る。`find?` 失敗時は `getD m` で `m` にフォールバック。
  - `Shape.gravity.of_isSettled' (hSettled hNorm) : IsSettled s ∧ IsNormalized s → gravity s = s` — ブリッジ axiom 1 本経由で証明。
  - ブリッジ `axiom floatingUnits_eq_nil_of_isSettled : IsSettled s → floatingUnits s = []` — 1 本に集約。Phase D-10D で `Internal/Collision.lean` の BFS 完全性 + `structuralCluster` 構造不変から theorem 化する。
- [`S2IL/Operations/Gravity.lean`](../../S2IL/Operations/Gravity.lean) facade: 旧 `axiom Shape.gravity.of_isSettled` を削除し、`Shape.gravity.of_isSettled` を新シグネチャ（`IsNormalized` 追加）の theorem として再公開。
- 残 axiom 構造: 旧 3 (`isSettled` / `of_isSettled` / `rotateCW_comm`) → 新 3 (`isSettled` / `floatingUnits_eq_nil_of_isSettled` / `rotateCW_comm`)。`of_isSettled` は theorem 化、ブリッジ axiom が 1 本に分解されたが、D-10D で 2 本同時に解消される構造。

**設計上の修正（重要）**: 当初 §1.2 / §6.2 の `IsSettled s → gravity s = s` は反例 `s = [L_grounded, L_empty]` を持つ。`IsSettled` は末尾空レイヤを禁止しないが、`gravity` 末尾の `Shape.normalize` は末尾空を必ず除去する。spec [`falling.md §6.6`](../shapez2/falling.md) は出力が正規形であることを要求しており、入力にも `IsNormalized s` を仮定するのが自然である（shape の構造的不変は本来 `IsNormalized` を含むべきだが、Greenfield では `Shape := List Layer` の abbrev で型レベル強制を避けたため、API 仮定で表現する）。

**反例検証**: [`Scratch/PhaseD10C_BehaviorCheck.lean`](../../Scratch/PhaseD10C_BehaviorCheck.lean) で:

- ブリッジ axiom の代表入力検証（settled 例 4・7・単独 Cr・空 Shape・水平接触のみ → `floatingUnits = []`）5 件 `#guard` パス
- 浮遊あり例（例 1・例 8）で `floatingUnits ≠ []` 2 件 `#guard` パス
- `landingDistance_le_minLayer` の境界値 (`minLayer = 0`、`minLayer = 5`) を `example` で型検査
- `IsNormalized` の境界（末尾空 Shape は非正規、0 層は正規）を `decide` で確認

ブリッジ axiom が偽でないことを spec 由来代表値で確認済み。

**GO 判定**: D-10D 着手可能。次は `Internal/Collision.lean` の BFS 完全性と `gravity.isSettled` 主証明。

### Phase D-10D: 安定性主定理 + ブリッジ補題 — 2〜3 セッション想定（最大ヤマ）

`Internal/Collision.lean` を完成させ、次の 2 本を同時に theorem 化:

1. **`gravity.isSettled`**: 出力安定性（旧計画通りの主目標）
2. **`floatingUnits_eq_nil_of_isSettled`** (D-10C で導入したブリッジ axiom): 安定入力に対する落下単位空集合性

両者は共通の補題 **`isGroundedFast_iff_isGrounded : isGroundedFast s p = true ↔ IsGrounded s p`** に帰着する。これは `groundingNeighbors` の BFS（fuel = `s.length * 4 + 4`）が `IsGroundingEdge` の `ReflTransGen` を完全に実現することの証明である。

**作業順序**:

1. `Internal/Collision.lean` で BFS の **soundness** (`isGroundedFast = true → IsGrounded`) と **completeness** (`IsGrounded → isGroundedFast = true`) を証明。
2. completeness から `floatingUnits_eq_nil_of_isSettled` を導出（`structuralCluster` メンバの非空・有効性 + IsSettled 適用）。これでブリッジ axiom が theorem 化され、`of_isSettled` が axiom-free になる。
3. soundness + dropOf 構造から `gravity.isSettled` を構成的に証明。「fold で配置した結果のすべての非空象限が `IsGrounded`」を `dropOf` から構成的に与える戦略。旧 `placeLDGroups_landing_groundingEdge_mono` に相当する内容だが、本モデルでは `dropOf` を 1 回計算した固定写像として扱うため、cross-group 上書きが構造的に発生しない（衝突判定で排除される）。

**最大の作業ノード**: BFS 完全性の証明（`ReflTransGen` 上の帰納法 → BFS 反復回数の有限性 → fuel 充足性）。

### Phase D-10E: 等変性 — 1 セッション想定

`Equivariance.lean` の主証明と facade 1 行系。`floatingUnits.rotateCW_comm` は
`clusterSet.rotateCW_comm` (Phase C) + `IsGrounded.rotateCW` (Phase D-1) の合成で
30 行程度に収まる見込み。

### Phase D-10F: 振り返り（10-R）— 0.5 セッション

[layer-ab-rewrite-plan.md §5](layer-ab-rewrite-plan.md) のチェックリストを Gravity に適用。
`_archive/pre-greenfield/Operations/Gravity*` の削除候補リストを作成し Phase E で削除。

---

## 8. リスクレジスタ

| # | リスク | 検知方法 | 緩和策 |
|---|---|---|---|
| R1 | `dropOf` の well-founded 再帰が `shareDirection` の循環で構築不能 | Phase D-10B で `decreasing_by` が閉じない | 「同方角列 + minLayer 厳密小」の半順序を明示。`shareDirection` を `≤` ではなく `<` で扱う |
| R2 | `CanDropBy` 衝突判定が pin と cluster の混在で漏れる | §4.1 の例 6 / 例 9 の不一致 | 衝突判定を「位置単位」に正規化し、unit 種別は positions の集合のみで扱う |
| R3 | `gravity.isSettled` の証明が `Relation.ReflTransGen` 帰納で爆発 | Phase D-10D で 3 セッション失敗 | 「全非空象限 → layer 0 への直線パス」を `dropOf` から構成的に与える代替戦略 |
| R4 | normalize と等変性の相互作用で末尾レイヤの扱いがズレる | §4.3 で `--------:--Cr----` 系の反例 | 等変性証明では normalize を最後に適用し、`normalize.rotateCW_comm` を別補題として独立証明 |
| R5 | Layer C / Machine から要求される派生定理（冪等性等）が漏れる | Phase D-10F の §5 チェックリストで API 不足 | `gravity.idempotent` / `gravity.layerCount_le` を facade に最初から含める |
| R6 | `decide` 経由のテストが遅すぎて反例検証が回らない | §4 で `vanilla4` 全列挙が 5 分超 | `Plausible` ランダムサンプルに切替、または `vanilla3` 相当の縮小設定を一時導入 |
| R7 | §4.1.1 の interlock パターン（特に I-3）で採用モデル (d) が誤った `dropOf` を返す | I-1/I-2/I-3 の `#eval gravity` が手計算 / 仕様トレースと不一致 | `dropOf` の well-founded 再帰の measure を「`shareDirection` で結ぶ minLayer の擬順序」と再定義。歯-ピンが同列で交互配置の場合は **個別ピンを独立 unit として処理** することで spec §6.4 の衝突安全性を保証（pin は単一象限なので順序内で衝突せず、最後に並ぶ） |

---

## 9. 完了条件（Phase D-10 GO/STOP 判定）

### GO（次フェーズへ）条件

- [x] §4 の 9 件の `#guard` テストがすべて通過（D-10B 完了時点）
- [x] §4.5 設計観点 7 項目チェック（D-10B 完了時点）
- [x] `landingDistance_le_minLayer` axiom-free 証明（D-10C 完了）
- [x] `gravity.of_isSettled` を `IsNormalized` 仮定で theorem 化（D-10C 完了、ブリッジ axiom 経由）
- [ ] `S2IL/Operations/Gravity.lean` 系の 3 axiom (`isSettled` / `floatingUnits_eq_nil_of_isSettled` / `rotateCW_comm`) が theorem 化
- [ ] `lake build` green、warning 0
- [x] §5 のファイル構成が遵守されている（facade ≤ 150 行、一般 ≤ 300 行）
- [ ] §6 の補題チェーンが全て埋まっている（sorry 0）
- [ ] [architecture-layer-ab.md §1.4.4](architecture-layer-ab.md) と本書が実装と一致
- [ ] `S2IL/_agent/sorry-plan.json` の axioms[] から Gravity の axiom が削除

### STOP（撤退・pivot）条件

- 3 セッション連続で同一補題が閉じない
- §4.1 の反例検証で **採用モデル (d) が仕様を満たさない** ことが判明
- `dropOf` の well-founded 再帰が Lean の `decreasing_by` で構築不能と判明

STOP 時は本書 §3.5 の (b) 完全宣言的アプローチに pivot する（gravity を `Classical.choose` で取り、別途 spec で性質を述べる）。

---

## 10. 関連

| 参照先 | 用途 |
|---|---|
| [architecture-layer-ab.md](architecture-layer-ab.md) §1.4.4 | 落下機構の構造的拘束 |
| [layer-ab-rewrite-plan.md](layer-ab-rewrite-plan.md) §4.3 | Phase D-10 の上位計画 |
| [docs/shapez2/falling.md](../shapez2/falling.md) | 落下仕様の正本 |
| [S2IL/Operations/Settled.lean](../../S2IL/Operations/Settled.lean) | `IsGrounded` / `IsSettled` の定義 |
| [S2IL/Kernel/Cluster.lean](../../S2IL/Kernel/Cluster.lean) | `ClusterRel` / `clusterSet` の定義 |
| [`/memories/repo/waveStep-grounding-mono-persistence.md`](#) | 旧 wave モデル破綻ノート |
| `_archive/pre-greenfield/Operations/Gravity/` | 過去の証明資産（§2.4 で個別評価） |
