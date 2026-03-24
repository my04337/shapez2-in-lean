# MaM (Make Anything Machine) の形式化

> 最終更新: 2026-03-26

---

## 1. MaM とは

**MaM (Make Anything Machine / 全自動工場)** は、Shapez2 のオペレーターレベルで要求される「任意のシェイプを自動生産する設備」のことである。

ゲームでは **ランダム図形 (Randomized Shape)** と呼ばれる毎回変化する目標が要求される。  
プレイヤーは **オペレーター図形レシーバー (Operator Shape Receiver)** で目標シェイプを論理信号として受け取り、MaM がその信号を解析して物理的なシェイプを産出する。

### 1-1. MaM の動作原理

MaM は以下の 2 フェーズで構成される。

#### フェーズ A: シミュレーション処理（信号処理）

**シミュレーション装置 (Simulated Machines)** を使い、論理信号内の目標シェイプを象限単位に分解する。

基本的な象限抽出パターン（NE 象限の例）:

```
目標シェイプ信号
    → シミュレーション切断処理機（West Half を削除 → NE, SE が残る）
    → シミュレーション逆回転機（CCW 90°回転 → 元の NE が NW 位置に）
    → シミュレーション切断処理機（West Half を削除 → 元の NE だけが残る）
```

これを NE / SE / SW / NW の全象限、かつ全シェイプ種別（Circle / Rectangle / Star / Windmill）に対して繰り返し、各象限・各種別が一致するかを論理回路で選択する。

#### フェーズ B: 物理生産（実機処理）

フェーズ A で取り出した「必要な象限・必要な種別」の信号を元に、実際の採掘機から採掘したシェイプを切断・回転・積層して目標形状を組み立て、着色機で色を付ける。

---

## 2. MaM が生成できるシェイプの範囲

標準モード（最大 4 レイヤ）における理論的な生成可能シェイプの範囲は以下のように段階的に広がる。

### 2-1. 無着色 1 レイヤシェイプ（基本 MaM）

最も基本的な MaM の目標。

- **象限数**: 4（NE / SE / SW / NW）
- **シェイプ種別**: 空 (empty) / Circle / Rectangle / Star / Windmill の 5 種
- **レイヤ数**: 1

1 レイヤシェイプの象限数と種別の組み合わせは最大 $5^4 = 625$ 通り（ただし全て空は正規化上無効）。  
基本 MaM はこのうち全てのシェイプを生成できることが要求される。

### 2-2. 着色 1 レイヤシェイプ

着色機 (Painter) と混色機 (Color Mixer) を組み合わせることで色付きシェイプも生成可能。

- **カラー種別**: 8 種（Red / Green / Blue / Cyan / Magenta / Yellow / White / Uncolored）
- 混色の非結合性（`mix_not_assoc`）により、全ての色は  
  「原色 (Red / Green / Blue)」の 3 色の組み合わせと White で生成できる

### 2-3. 多レイヤシェイプ

積層機 (Stacker) を繰り返し使うことで最大 4 レイヤのシェイプを生成できる。

- **ピン (Pin)** を使うと象限をレイヤ方向に「底上げ」できる  
  （ピン押し機 (Pin Pusher) による操作）
- **結晶 (Crystal)** を含むシェイプは CrystalGenerator を経由する  
  （積層時に結晶は全て砕け散る）

---

## 3. Lean による形式化に必要な定理

MaM の形式化・正しさの証明には以下の定理群が必要になる。

### 3-1. 各操作の正確な定義（実装済み）

| 操作 | Lean の定義 | 備考 |
|---|---|---|
| 切断処理機 | `Shape.halfDestroy` | `S2IL/Behavior/Cutter.lean` |
| 切断機 | `Shape.cut` | `S2IL/Behavior/Cutter.lean` |
| 回転機 | `Shape.rotateCW` | `S2IL/Behavior/Rotate.lean` |
| 逆回転機 | `Shape.rotateCCW` | `S2IL/Behavior/Rotate.lean` |
| 180° 回転機 | `Shape.rotate180` | `S2IL/Behavior/Rotate.lean` |
| 積層機 | `Shape.stack` | `S2IL/Behavior/Stacker.lean` |
| 着色機 | `Shape.paint` | `S2IL/Behavior/Painter.lean` |
| ピン押し機 | `Shape.pinPush` | `S2IL/Behavior/PinPusher.lean` |
| 結晶製造機 | `Shape.crystallize` | `S2IL/Behavior/CrystalGenerator.lean` |
| 落下処理 | `Shape.gravity` | `S2IL/Behavior/Gravity.lean` |

これらは `Machine` 名前空間でまとめて `Option` 対応ラッパーとして提供される（`S2IL/Machine/Machine.lean`）。

### 3-2. 象限抽出の正しさ（未着手）

MaM の核心は「任意の象限を他の象限と独立に抽出できる」ことである。

```
-- 必要となる補題の例 (NE 象限抽出)
-- halfDestroy(rotateCCW(halfDestroy(s))).layer[0].ne = s.layer[0].ne
```

具体的には以下の補題を用いた連鎖証明が必要となる。

| # | 必要な補題 | 概要 |
|---|---|---|
| T-1 | `halfDestroy_east_half` | 切断処理後の東半分が元のシェイプの NE・SE と一致する |
| T-2 | `rotateCCW_ne_maps_to_nw` | CCW 回転後に元の NE 象限が NW 位置に移動する |
| T-3 | `halfDestroy_after_rotate_isolation` | 2 回の切断処理で単一象限が分離されることを証明 |
| T-4 | `quarter_extraction_completeness` | 全象限について T-1〜T-3 が成立する |

### 3-3. 積層の正しさ（部分的に実装済み）

積層機に関して以下の性質が必要。

| # | 定理名（予定） | 概要 | 状態 |
|---|---|---|---|
| T-5 | `stack_correct_no_float` | 浮遊なし入力のスタック結果が正しい | ⬜ 未着手 |
| T-6 | `stack_correct_single_quarter` | 単一象限シェイプのスタックが正しい | ⬜ 未着手 |
| T-7 | `stack_layerCount_bound` | スタック結果のレイヤ数が上限以下 | ✅ `placeAbove_layerCount` で基礎済み |

### 3-4. 操作の等変性（一部証明済み・一部未着手）

「同じ操作を別の向きで行っても、回転してから操作しても同じ」という等変性定理群。  
MaM が扱うシェイプの方向依存性をなくすために重要。

| # | 定理名 | 概要 | 状態 |
|---|---|---|---|
| T-8 | `rotateCW_rotate180_comm` | `rotateCW(s.rotate180) = (rotateCW s).rotate180` | ✅ 証明済み |
| T-9 | `cut_rotate180_comm` | 切断と 180° 回転の可換性 | ✅ 証明済み |
| T-10 | `gravity_rotate180_comm` | 落下処理と 180° 回転の可換性 | 🔄 最終 sorry 残り（後述） |
| T-11 | `stack_rotate180_comm` | `stack(s, t).rotate180 = stack(s.rotate180, t.rotate180)` | ⬜ T-10 依存 |
| T-12 | `paint_rotate180_comm` | 着色と 180° 回転の可換性 | ⬜ 未着手 |

### 3-5. MaM 完全性（未着手）

最終的なゴールとなる定理群。

| # | 定理名（予定） | 概要 | 状態 |
|---|---|---|---|
| T-13 | `mam_produces_any_uncolored_1layer` | 任意の無着色 1 レイヤシェイプを MaM は生成できる | ⬜ 未着手 |
| T-14 | `mam_produces_any_colored_1layer` | 着色も含めた 1 レイヤシェイプを生成できる | ⬜ 未着手 |
| T-15 | `mam_produces_any_multilayer` | 多レイヤシェイプを生成できる（レイヤ制限内） | ⬜ 未着手 |

---

## 4. `process_rotate180` の立ち位置

### 4-1. 定理の内容

`process_rotate180`（公開名: `gravity_rotate180_comm`）は次の等変性を主張する:

```lean
theorem gravity_rotate180_comm (s : Shape) :
    (s.gravity).map Shape.rotate180 = s.rotate180.gravity
```

すなわち「あるシェイプに落下処理を施した後に 180° 回転させた結果」と  
「あるシェイプを 180° 回転させた後に落下処理を施した結果」が一致する、という定理である。

### 4-2. 積層等変性のブロッカー

積層機は以下の処理パイプラインで実装される。

```
stack(bottom, top)
    = gravity(shatter_top_crystals(placeAbove(bottom, top)))
```

このため、積層と回転の可換性（T-11）は `gravity_rotate180_comm`（T-10）に依存する。  
T-11 が証明されなければ、T-13 以降の MaM 完全性証明に進めない。

### 4-3. プロジェクト全体における位置

プロジェクト全体で残っている `sorry` は現在 **1 件**であり、それが `process_rotate180` である。

証明の残課題は次の 1 ゴールに絞られている:

> 「同一の obstacle 上で、  
> `sortFallingUnits((floatingUnits s).map FallingUnit.rotate180)` を順に畳み込んだ結果と  
> `sortFallingUnits(floatingUnits s.rotate180)` を順に畳み込んだ結果が一致すること」

両リストは **同じ位置集合** を表すが、BFS 発見順の差異により要素順が異なる場合がある。  
その順序差が落下結果に影響しないこと（tied 要素の可換性）の形式化が未完了である。  
詳細は [`docs/gravity-rotate180-proof-plan.md`](../gravity-rotate180-proof-plan.md) を参照。

---

## 5. 形式化の依存関係グラフ（概要）

```
各操作の正確な定義（実装済み）
    │
    ├─ 象限抽出の正しさ (T-1〜T-4) ─────────────────────┐
    │                                                     │
    ├─ gravity_rotate180_comm (T-10) ← process_rotate180  │
    │       │                          (sorry 残り1件)    │
    │       ▼                                             │
    │   stack_rotate180_comm (T-11)                       │
    │       │                                             │
    │       ▼                                             ▼
    └─── paint_rotate180_comm (T-12) ──→  MaM 完全性 (T-13〜T-15)
```

`process_rotate180` の解消が、MaM 形式化への道を開く最後の 1 ピースである。
