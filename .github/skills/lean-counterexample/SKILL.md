---
name: lean-counterexample
description: >
  Catalog of boundary-value and 3-element interaction tests for counterexample search,
  plus GameConfig tier guidance (vanilla4 / vanilla5 / stress8).
  Use when: check counterexample, verify theorem, is this true, validate lemma,
  false theorem, counterexample search, theorem verification, check if provable,
  反例, 反例チェック, 真偽確認.
  Returns: test-case catalog by type + tier selection table.
  Don't call when: you want the agent to actually run the checks (use agent `lean-sorry-investigator`).
metadata:
  argument-hint: 'Reference: counterexample test catalog'
---

# 反例チェックスキル

定理の真偽をコーディング着手前に体系的な反例探索で確認し、偽定理への投資を早期に打ち切る。

## GameConfig 層数の指針

反例チェックの層数は **速度と網羅性のトレードオフ** で選択する。

| ティア | GameConfig | 層数 | 想定 Shape 数 | 所要時間目安 | 用途 |
|--------|------------|------|---------------|-------------|------|
| **デフォルト** | `vanilla4` | 4 | ~6,500–65,000 | **2–25 s** | 試行錯誤フェーズの高速チェック |
| **拡張** | `vanilla5` | 5 | ~59,000–1M+ | **30–60 s** | 最終確認・コミット前検証 |
| **ストレス** | 8L カスタム | 8 | ~65,000 | **~17 s** | 複雑な性質の最終砦（最小ジェネレータ使用） |

### 使い分けルール

1. **通常の反例探索**: `vanilla4` (4L) をデフォルトで使用
2. **最終確認**: 証明を sorry → 定理に昇格させる前に `vanilla5` (5L) で再検証
3. **高リスク性質**: ソート順序・3 要素相互作用など複雑な不変量は `vanilla5` + 8L ストレスも実施
4. `stress8` (8L) は大規模だが 4^n ジェネレータなら 65,536 shapes / ~17s で現実的

### ジェネレータの選択

| ジェネレータ | Shape 数 (4L) | Shape 数 (5L) | 特徴 |
|-------------|---------------|---------------|------|
| 2方角×2パターン (4^n) | 256 | 1,024 | 最も高速・ストレス向き |
| 2方角×3パターン (9^n) | 6,561 | 59,049 | 色付き Quarter を含む標準的な検証 |
| 4方角×2パターン (16^n) | 65,536 | 1,048,576 | 方角の網羅性が高いがコスト大 |

> **ベンチマーク根拠** (2025-06-07 測定):
> 4L/9^4=2.5s, 5L/9^5=31s, 4L/16^4=25s, 8L/4^8=17s

## 手順

### 1. 量化変数の特定

定理のシグネチャから量化された変数・仮定・結論を明確にする。

### 2. テストケースの列挙

| 型 | テストケース |
|---|---|
| `List α` | `[]`, `[x]`, `[x, y]` |
| `Layer` | 各方角の組み合わせ（最大 16 パターン） |
| `Shape` | 空、1〜4 レイヤ（デフォルト vanilla4） |
| `QuarterPos` | `.ne`, `.nw`, `.se`, `.sw` (全4値) |
| `Nat` | `0`, `1`, `2`, 大きい値 |
| `Option α` | `none`, `some x` |

有限型は全探索が望ましい。

### 2a. 有限型の高速パス

量化された変数が **有限型**（`Bool`, `Fin n`, カスタム `inductive` で `[DecidableEq]`/`[Fintype]` あり等）の場合、`decide` による全探索を第一選択とする。

**判定基準**: 型が以下のいずれかに該当すれば有限型として全探索可能:
- `Fin n` (`n` が小さい — 目安 `n ≤ 256`)
- `Bool`, `Unit`, `Empty`
- `Decidable` インスタンスを持つ `Prop`
- カスタム `inductive` で要素数が有限（`[Fintype]` あり）
- 上記の `Prod` / `Sum` / `Option`

```lean
-- 全探索: decide で一発
example : ∀ b : Bool, b || !b = true := by decide

-- Fintype.elems で列挙 → #eval で全パターンテスト
#eval (Fintype.elems : Finset (Fin 4)).toList.all fun i =>
  i.val + 0 == i.val
```

**無限型の場合**: `decide` は使えないので下記 Step 2b または `#eval` にフォールバックする。

### 2b. 無限型の高速パス（`plausible` タクティク）

量化された変数が **`Nat`, `Int`, `List Nat`** 等の無限型で、かつ型が `Arbitrary` インスタンスを持つ場合、
`plausible` タクティクによるランダムサンプリングが有効。

```lean
-- Nat を含む全称命題を plausible で素早く確認
example : ∀ n : Nat, n ≤ n + 1 := by plausible
-- → "Unable to find a counter-example" ならほぼ真（証明ではない）

-- 偽命題の反例検出
example : ∀ n : Nat, n + 1 = n := by plausible
-- → "Found a counter-example! n := 0"
```

**注意**:
- `plausible` は**証明ではない**。反例なし = 「真っぽい」の確認のみ
- S2IL の全主要型（`Color`, `Quarter`, `Layer`, `Shape`, `Direction`, `QuarterPos`, `GameConfig` 等）は `S2IL/Shape/Arbitrary.lean` で `SampleableExt` インスタンス定義済み。`import S2IL` でそのまま利用可能
- 有限型（`Direction`, `QuarterPos` 等）は `decide` で全探索が確実（`plausible` より優先）
- 詳細: [`docs/lean/plausible-guide.md`](../../../docs/lean/plausible-guide.md)

### 3. 機械検証

#### 【推奨】REPL による高速検証（~11-20s 初回起動）

```jsonl
{"cmd": "#eval Direction.all.map Direction.rotate180", "env": 0}
```

```powershell
# Persistent モード（推奨・~600ms/回）
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands-<sessionId>.jsonl

# バッチモード（レガシー）
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands-<sessionId>.jsonl
```

（macOS/Linux の `.sh` 版も存在。引数はほぼ同型）

▶ stdout 例（`data` に結果リスト）:

```
{"env":0}
{"messages":[{"severity":"info","data":"[Direction.sw, Direction.nw, Direction.ne, Direction.se]"}],"env":1}
```

`data` フィールドが期待値と異なれば反例あり。

#### `#eval` による検証

```lean
#eval do
    let cases := [case1, case2, case3]
    for c in cases do
        if !(checkProperty c) then
            IO.println s!"反例発見: {c}"
```

#### `decide` による全探索（有限型）

```lean
example : ∀ q : QuarterPos, P q := by decide
```

#### Scratch ファイル（大規模チェック用 fallback）

複数定義・10 行超の検証コードは `Scratch/` に配置して `lake env lean` で実行:

```lean
-- Scratch/FooCheck.lean
import S2IL
open Direction
#eval Direction.all.all (fun d => d.rotate180.rotate180 == d)
-- true なら全ケース OK、false なら反例あり（個別出力で特定する）
```

```powershell
lake env lean Scratch/FooCheck.lean
```

### 4. 結果の判定

| 結果 | 意味 |
|---|---|
| `#eval` が期待値と一致 | その入力では成立（反例なし） |
| `#eval` が予期しない値を返す | **反例発見** → シグネチャを修正 |
| `decide` が `true` | 有限全探索で成立を確認 |
| `decide` が `false` または `Decidable` インスタンスなし | 反例あり / 全探索不可 → `#eval` で個別探索 |
| `plausible` が "Unable to find a counter-example" | ランダムテスト通過（証明ではない）→ 証明着手OK |
| `plausible` が "Found a counter-example!" | **反例発見** → シグネチャを修正 |
| REPL の `messages[].severity == "error"` | 型エラー等 → コードを修正してから再テスト |

```powershell
lake env lean Scratch/FooCheck.lean
```

### 4. 反例発見時の対応

1. **最小化**: 不要な変数を除去
2. **修正案**: 仮定の追加 / 結論の弱化 / 撤回
3. **修正後の再チェック**

### 5. N 要素の相互作用チェック（3-cycle 検出）

ペアワイズ検証だけでは不十分。3 要素以上の組み合わせも確認する。グリーディアルゴリズム・ペアワイズ条件の定理では第三者による遮断ケースを必ずチェックする。

## Gotchas

- `#eval` は `Decidable` でない `Prop` には使えない → `Bool` 関数に変換
- `sorry` を含むコードの `#eval` 結果は信頼できない
- `BEq` ≠ `DecidableEq`（計算的等価性 vs 命題的等価性）

## 関連

**lean-proof-planning**（証明戦略の全体フロー） / **lean-sorry-investigator** サブエージェント（自動反例チェック + タクティク試行 + 補題探索を一括実行）
