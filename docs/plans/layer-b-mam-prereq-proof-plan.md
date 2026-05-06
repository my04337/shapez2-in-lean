# Layer B MAM 前提証明 追加計画

> 作成日: 2026-05-06
> 最終更新: 2026-05-06

## TODO リスト

| ID | 状態 | やるべきこと | 完了条件 |
|---|---|---|---|
| TODO-1 | 未着手 | `halfDestroy -> rotate* -> halfDestroy` の方角仕様を反例チェックで確定する | 元象限と出力方角の対応表が REPL / `#eval` で確認済み |
| TODO-2 | 未着手 | T-1〜T-4 の象限抽出 theorem を追加する | `S2IL.Operations` facade から shape-level theorem を参照できる |
| TODO-3 | 未着手 | T-5〜T-6 の stacker correctness theorem を追加する | `Shape.stack.isSettled` と単一象限積層 theorem の型確認が通る |
| TODO-4 | 未着手 | T-7 の `Shape.stack.layerCount_le` と補助補題を追加する | `stack` 全体のレイヤ数上界が public theorem になる |
| TODO-5 | 未着手 | Layer A/B 正本へ、確定した API 境界・分割方針・等変性例外を追記する | [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) が追加実装後の構造と一致する |
| TODO-6 | 未着手 | 局所ビルド、全体ビルド、sorry-goals 更新を確認する | `build.ps1` が成功し、`S2IL/_agent/sorry-goals.md` が 0 件のまま |

## Current Focus

| 項目 | 値 |
|---|---|
| 対象 theorem | `Shape.quadrantExtraction_*` / `Shape.stack_*`（新規追加予定） |
| 位置 | `S2IL/Operations/QuadrantExtraction.lean`（新規） / `S2IL/Operations/Stacker.lean` |
| 既存 sorry | なし。`S2IL/_agent/sorry-goals.md` は 0 件 |
| 構造化 | 実装時に sorry を置く場合のみ `S2IL/_agent/sorry-plan.json` を整備する |

**次アクション**:
1. `halfDestroy -> rotate* -> halfDestroy` がどの象限をどの方角に残すかを REPL / `#eval` で固定する。
2. T-1〜T-4 の象限抽出 theorem を先に追加し、その後 T-5〜T-7 の stacker correctness に進む。

---

## 目標

`docs/shapez2/mam.md` §4-1〜§4-4 と §5 を、現行 Lean 実装と照合した結果に基づき、Layer B に不足している MAM 前提証明を追加する。

Layer A/B の正本は [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) である。本計画は追加対処の作業計画に留め、実装で確定した API 境界、ファイル分割、MECE 分類、等変性の例外規則は、区切りの良いタイミングで正本へ追記する。

対象は以下に限定する。

| 対象 | 扱う範囲 |
|---|---|
| 象限抽出 | `halfDestroy` / `rotateCW` / `rotateCCW` / `rotate180` を使った単一象限抽出の正しさ |
| 積層正しさ | `Shape.stack` の安定化・レイヤ上界・単一象限入力に対する挙動 |
| 等変性の棚卸し | 既存 theorem の有無と、E/W 参照操作の例外扱いを明確化する |

対象外:

- `mam.md` §4-5 の MAM 能力分類・tier 完全性 (T-13〜T-17)
- Layer C の Flow 評価関数・台数計算・ワイヤー制御
- `cut` / `halfDestroy` の CW 等変性を新規証明すること。これは E/W 参照操作なので不成立であり、180° 等変性だけを扱う

---

## 精査結果

| `mam.md` 項目 | 現状 | Lean 側の証拠 | 追加対処 |
|---|---|---|---|
| 4-1 操作定義 | 実装済み | `S2IL/Operations.lean` facade が各操作を公開 | なし |
| T-1 東半分の保存 | 基礎補題はあるが、MAM 用 theorem として未整理 | `Layer.eastHalf_apply`, `Shape.eastHalf_cons` | QX-1 |
| T-2 象限の回転変位 | 回転・位置補題はあるが、抽出工程の theorem は未整理 | `Layer.rotateCW_apply`, `QuarterPos.getQuarter_rotateCW` | QX-2 |
| T-3 2 段切断による象限分離 | 未実装 | `halfDestroy` 合成の公開 theorem は未発見 | QX-3 |
| T-4 象限抽出の完全性 | 未実装 | 全象限を覆う抽出 theorem は未発見 | QX-4 |
| T-5 浮遊なし入力の積層 | 未実装 | `Shape.stack` は定義済みだが、安定入力 / 中間形状に関する public theorem は未発見 | ST-1, ST-2 |
| T-6 単一象限積層 | 未実装 | 単一象限 predicate / constructor と stacker theorem は未発見 | ST-3 |
| T-7 積層のレイヤ数上界 | 部分的 | `Shape.truncate.layerCount_le` はあるが、`Shape.stack.layerCount_le` は未発見 | ST-4 |
| T-8 回転操作間の整合性 | 実装済み | `Shape.rotateCW.four`, `Shape.rotate180_eq_rotateCW_rotateCW`, `Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW` | なし |
| T-9 切断の等変性 | 180° のみ実装済み。CW は不成立 | `Shape.cut.rotate180_comm`, `Shape.halfDestroy.rotate180_comm`; `architecture-layer-ab.md` §1.4.1 | なし。`mam.md` 側の表現修正候補 |
| T-10 落下処理の等変性 | 実装済み | `Shape.gravity.rotateCW_comm` / `rotate180_comm` / `rotateCCW_comm` | なし |
| T-11 積層の等変性 | 実装済み | `Shape.stack.rotateCW_comm` / `rotate180_comm` / `rotateCCW_comm` | なし。`mam.md` 側の表現修正候補 |
| T-12 着色の等変性 | 実装済み | `Shape.paint.rotateCW_comm` / `rotate180_comm` / `rotateCCW_comm` | なし |

結論として、§4-4/§5 の「等変性不足」は現行 Lean ではほぼ解消済みである。一方で、§4-2 の象限抽出と §4-3 の stacker correctness は、MAM 完全性の前段 theorem としてまだ不足している。

---

## Phase QX: 象限抽出 theorem

### QX-0. 方角仕様の確定

最初に、`Direction := Fin 4` の順序と `Layer.rotateCW` の向きを、MAM 文書の NE / SE / SW / NW 表記と対応させる。

現行定義では:

- `Layer.mk ne se sw nw` は `0=NE`, `1=SE`, `2=SW`, `3=NW`
- `Layer.rotateCW l d = l (d - 1)`
- `Shape.halfDestroy = Shape.eastHalf` で、`0=NE`, `1=SE` を残す

このため、`halfDestroy -> rotateCCW -> halfDestroy` が「元の NE」を残す、という命題は証明前に必ず反例チェックする。MAM 用 theorem は、どの元象限がどの出力方角に残るかを固定してから命名する。

### QX-1. halfDestroy の点ごと仕様

候補 theorem:

| theorem | 役割 |
|---|---|
| `Layer.eastHalf_preserves_east` | `d.val < 2` なら `Layer.eastHalf l d = l d` |
| `Layer.eastHalf_clears_west` | `2 <= d.val` なら `Layer.eastHalf l d = Quarter.empty` |
| `Shape.halfDestroy_get` | layer index と direction を指定した shape レベル仕様 |

既存の `Layer.eastHalf_apply` を正本にし、MAM 用の読みやすい theorem 名を薄く追加する。

### QX-2. 回転による方角変位

候補 theorem:

| theorem | 役割 |
|---|---|
| `Layer.rotateCW_getDir` | `rotateCW` 後の direction が元のどの direction を参照するか |
| `Layer.rotateCCW_getDir` | `rotateCCW` 版 |
| `Layer.rotate180_getDir` | `rotate180` 版 |

既存の `Layer.rotateCW_apply` と `QuarterPos.getQuarter_rotateCW` から導出する。

### QX-3. 2 段切断の単一象限分離

候補 theorem:

| theorem | 役割 |
|---|---|
| `Shape.extractAfterRotateCW_getDir` | `halfDestroy -> rotateCW -> halfDestroy` の点ごと仕様 |
| `Shape.extractAfterRotateCCW_getDir` | `halfDestroy -> rotateCCW -> halfDestroy` の点ごと仕様 |
| `Shape.extractAfterRotate180_getDir` | 必要なら 180° 版 |

「抽出された象限を元の位置に戻す」のか、「単一象限として別方角に置く」のかを theorem 名で分ける。MAM の選択回路に必要なのは、最終方角よりも「元象限以外が空になる」ことなので、位置固定版と存在版を分離する。

### QX-4. 全象限抽出の完全性

候補 theorem:

| theorem | 役割 |
|---|---|
| `Shape.quadrantExtraction_complete` | 任意の `d : Direction` について、その象限だけを残す固定工程が存在する |
| `Shape.quadrantExtraction_sound` | 抽出工程が元象限の値を保存し、他象限を空にする |

この段階で Layer C の代表フロー `halfDestroyer -> reverseRotator -> halfDestroyer` と接続し、Flow 側の example theorem へ渡せる shape-level 仕様を用意する。

---

## Phase ST: Stacker correctness

### ST-1. stack 出力の安定化

候補 theorem:

| theorem | 役割 |
|---|---|
| `Shape.stack.isSettled` | `Shape.stack bottom top config` は常に `IsSettled` |

証明方針:

1. `Shape.stack` を展開する
2. `Shape.gravity.isSettled` を適用する

### ST-2. 浮遊なし中間形状での stack 正しさ

候補 theorem:

| theorem | 役割 |
|---|---|
| `Shape.stack_eq_intermediate_of_IsSettled` | `placeAbove -> truncate -> shatterTopCrystals` 後が settled かつ normalized なら、`stack` はその中間形状と等しい |

証明方針:

1. 中間形状 `m := Shape.shatterTopCrystals (Shape.truncate (Shape.placeAbove bottom top) config) config.maxLayers` を局所定義する
2. `Shape.gravity.of_isSettled` を使う
3. `Shape.IsNormalized m` が必要になるため、`truncate` / `shatterTopCrystals` / `normalize` との接続補題を確認する

### ST-3. 単一象限積層

候補 theorem は、QX の single-quadrant predicate 確定後に命名する。

必要な前提の候補:

| 前提 | 意味 |
|---|---|
| `IsSingleQuadrantShape s d q` | `s` が方向 `d` に `q` だけを持つ 1 レイヤ shape |
| `q` が通常パーツまたは pin | crystal shatter の影響を避ける範囲を先に証明する |
| `config.maxLayers` が十分大きい | truncate による消失を避ける |
| 中間形状が settled | `gravity.of_isSettled` を適用する |

最初は crystal を含まない通常象限に限定し、結晶・pin を含む版は反例チェック後に広げる。

### ST-4. stack のレイヤ数上界

候補 theorem:

| theorem | 役割 |
|---|---|
| `Shape.stack.layerCount_le` | `(Shape.stack bottom top config).layerCount <= config.maxLayers` |

必要になりそうな補助 theorem:

| theorem | 役割 |
|---|---|
| `Shape.shatterTopCrystals.layerCount_le` | shatter が layerCount 上界を増やさない |
| `Shape.gravity.layerCount_le` | gravity が layerCount を増やさない |

既存の `Shape.truncate.layerCount_le` だけでは `Shape.stack` 全体の public theorem には届かないため、Layer B の補助補題として追加する。

---

## 実装配置

| ファイル | 追加内容 |
|---|---|
| `S2IL/Operations/QuadrantExtraction.lean` | QX theorem 群。`Cutter` / `Rotator` / `Kernel.Transform` の薄い合成仕様 |
| `S2IL/Operations.lean` | `QuadrantExtraction` の import と facade 目次追記 |
| `S2IL/Operations/Stacker.lean` | ST-1〜ST-4 の public theorem。行数が膨らむ場合は `S2IL/Operations/Stacker/Behavior.lean` へ分割 |
| `Test/Operations/QuadrantExtraction.lean` | QX の representative examples と theorem 型確認 |
| `Test/Operations/Stacker.lean` | ST theorem の型確認と small examples |

---

## 検証手順

証明作業の開始時は、REPL 試行前に局所ビルドで `.olean` を最新化する。

```powershell
.github/skills/lean-tooling/scripts/build.ps1 -Target S2IL.Operations
```

追加実装後の標準確認:

```powershell
.github/skills/lean-tooling/scripts/build.ps1 -Target S2IL.Operations
.github/skills/lean-tooling/scripts/build.ps1 -Target Test.Operations.QuadrantExtraction
.github/skills/lean-tooling/scripts/build.ps1 -Target Test.Operations.Stacker
```

最後に全体確認:

```powershell
.github/skills/lean-tooling/scripts/build.ps1
```

---

## 完了条件

| ID | 完了条件 |
|---|---|
| QX-DONE | T-1〜T-4 に対応する shape-level theorem が `S2IL.Operations` facade から参照できる |
| ST-DONE | T-5〜T-7 に対応する stacker correctness theorem が public API として参照できる |
| EQ-DONE | T-8〜T-12 の等変性棚卸しが `mam.md` と Layer A/B architecture で矛盾しない |
| BUILD-DONE | `build.ps1` 全体ビルドが成功し、`S2IL/_agent/sorry-goals.md` が 0 件のまま更新される |
