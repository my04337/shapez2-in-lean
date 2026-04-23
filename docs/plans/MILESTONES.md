# マイルストーン

Shapez2 in Lean (S2IL) プロジェクトの最終目標と、そこへ至る大きな塊を整理した計画書。

> 各項目の進捗（ビルド状況・残 sorry など）は扱わない。リアルタイム状態は [`S2IL/_agent/sorry-goals.md`](../../S2IL/_agent/sorry-goals.md)（自動生成）および [`S2IL/_agent/sorry-plan.json`](../../S2IL/_agent/sorry-plan.json) を参照。

---

## 最終目標

**MAM (Make Anything Machine) の形式化と完全性証明** を頂点とし、その基盤として Shapez2 の加工モデル全体を Lean 4 で定義・検証する。

頂点の定理（MAM 完全性）:

1. 任意の無着色 1 レイヤシェイプを MAM で生成できる
2. 任意の着色 1 レイヤシェイプを MAM で生成できる
3. 任意の多レイヤシェイプを MAM で生成できる（レイヤ上限内）

---

## 構造

大きく 4 つの層に分けて進める。層内の詳細度は「Lean コード上のディレクトリ / モジュール」と整合させる。

```
Layer D (MAM)              ← 3 つの完全性定理
    ↑
Layer C (Flow)             ← 加工フロー / ワイヤーネットワーク
    ↑
Layer B (Behavior)         ← 振る舞い系証明（落下・砕け散り・安定化）
    ↑
Layer A (Data & Operations) ← 静的データ型と純粋関数
```

---

## Layer A: データ型と加工操作の静的な定義

### A-1. Shape Code Notation

| 項目 | 概要 |
|---|---|
| A-1-1 | Part Code / Color / Quarter / Layer / Shape の型定義 |
| A-1-2 | Shape Code 文字列とのパース・シリアライズ関数 |
| A-1-3 | ラウンドトリップ定理（parse ∘ serialize = id） |

### A-2. 加工操作（純粋関数としての定義）

振る舞いに依存しない加工操作。

| 項目 | 概要 |
|---|---|
| A-2-1 | Half-Destroyer / Cutter / Swapper |
| A-2-2 | Rotator (CW / CCW / 180°) |
| A-2-3 | Painter と Color Mixer |
| A-2-4 | Stacker の placeAbove（積層の事前変形、重力処理は Layer B） |
| A-2-5 | Pin Pusher の変形部（重力処理は Layer B） |
| A-2-6 | Crystal Generator（結晶充填）|

### A-3. Wires and Logic の静的定義

論理回路の値と素子を純粋関数として定義。

| 項目 | 概要 |
|---|---|
| A-3-1 | Logical Signal の型（Number / Color / ShapeCode / Empty / Conflict） |
| A-3-2 | AND / OR / NOT / XOR / Comparison ゲート |
| A-3-3 | Belt Filter / Pipe Gate / Signal Producer |
| A-3-4 | Simulated Buildings（シミュレーション装置）群 |

---

## Layer B: 振る舞い系証明

時間発展や終端条件を伴うため、Layer A と切り分けて集中的に扱う。

### B-1. 落下 (Gravity)

| 項目 | 概要 |
|---|---|
| B-1-1 | 落下処理 `gravity` の定義と終端性 |
| B-1-2 | 落下の CW 回転等変性（rotate180 は帰結として導出） |

### B-2. 結晶の砕け散り (Crystal Shatter)

| 項目 | 概要 |
|---|---|
| B-2-1 | `shatterOnCut` / `shatterOnTruncate` の定義 |
| B-2-2 | BFS による結晶連結成分の抽出と、その完全性 |
| B-2-3 | Shatter の CW 回転等変性 |

### B-3. 安定化 (Settlement / IsSettled)

| 項目 | 概要 |
|---|---|
| B-3-1 | `IsSettled`（落下で変化しない状態）の定義 |
| B-3-2 | 落下出力が安定化していること（`gravity_IsSettled`） |
| B-3-3 | 安定化の CW 回転等変性 |

### B-4. 振る舞いを伴う複合操作

Layer B の基盤を使って証明される加工装置。

| 項目 | 概要 | 依存 |
|---|---|---|
| B-4-1 | Stacker の振る舞い（`placeAbove` → `shatterOnTruncate` → `gravity`） | B-1, B-2, B-3 |
| B-4-2 | Cutter / HalfDestroy の `settleAfterCut` | B-1, B-3 |
| B-4-3 | Swapper（両側の `settleAfterCut`） | B-1, B-3 |
| B-4-4 | Pin Pusher の `truncated.gravity` | B-1 |

### B-5. 等変性の統一

等変性は **CW 回転を基本単位**として各操作につき 1 本だけ証明し、他の回転は帰結として機械的に導出する。これにより証明チェーンの重複を排除する。

| 項目 | 概要 |
|---|---|
| B-5-1 | CW 回転等変性の統一インターフェース（各操作につき 1 本） |
| B-5-2 | `rotate180 = rotateCW ∘ rotateCW` を通じた 180° 等変性の機械導出 |
| B-5-3 | 必要に応じて CCW 等変性の機械導出（3 回 CW） |

---

## Layer C: 加工フロー

### C-1. Shape Processing フロー

| 項目 | 概要 |
|---|---|
| C-1-1 | 加工装置を接続するグラフ / パイプライン型 |
| C-1-2 | フローの評価関数（入力シェイプ → 出力シェイプ） |
| C-1-3 | 代表フロー（例: 切断 → 回転 → 切断 による象限分解）の検証 |
| C-1-4 | フロー等価性の定義と補助補題 |

### C-2. Wires and Logic フロー

| 項目 | 概要 |
|---|---|
| C-2-1 | ワイヤーネットワーク型 |
| C-2-2 | ネットワーク評価関数（入力信号 → 出力信号） |
| C-2-3 | 代表回路（比較ゲートによる条件分岐など）の検証 |

---

## Layer D: MAM

### D-1. ワイヤー系との統合

| 項目 | 概要 |
|---|---|
| D-1-1 | Belt Filter / Pipe Gate によるフロー制御の統合 |
| D-1-2 | 信号による動的フロー（条件付き加工）の表現 |
| D-1-3 | Operator Shape Receiver の定義 |

### D-2. 既存 MAM の形式化

| 項目 | 概要 |
|---|---|
| D-2-1 | 既知の MAM 設計を Lean で記述 |
| D-2-2 | MAM 出力をゲーム内挙動と照合 |

### D-3. MAM 完全性（最終目標）

| 項目 | 概要 |
|---|---|
| D-3-1 | 任意の無着色 1 レイヤシェイプを MAM で生成できる |
| D-3-2 | 任意の着色 1 レイヤシェイプを MAM で生成できる |
| D-3-3 | 任意の多レイヤシェイプを MAM で生成できる（レイヤ上限内） |

### D-4. MAM 設計支援

| 項目 | 概要 |
|---|---|
| D-4-1 | ある MAM が生成可能なシェイプ集合を算出する関数 |
| D-4-2 | 目標シェイプから加工手順を逆算するソルバー |
| D-4-3 | ソルバー出力の健全性（求めた手順で目標シェイプが得られる） |

---

## 関連計画ファイル

| ファイル | 概要 |
|---|---|
| [architecture-layer-ab.md](architecture-layer-ab.md) | Layer A/B の新ディレクトリ構造と設計原則の正本 |
| [layer-ab-rewrite-plan.md](layer-ab-rewrite-plan.md) | Layer A/B Greenfield 再構築の Phase 別実施計画 |
| [archive/gravity-greenfield-rewrite-plan.md](archive/gravity-greenfield-rewrite-plan.md) | 旧 Gravity 限定再構築計画（`layer-ab-rewrite-plan.md` に統合済み）|

将来的に層ごとの個別計画が必要になった場合、`docs/plans/` に追加する（ケバブケース命名）。
