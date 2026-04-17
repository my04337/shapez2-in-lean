# Plausible 活用ガイド（S2IL プロジェクト向け）

> **関連**: [lean-counterexample スキル](../../.github/skills/lean-counterexample/SKILL.md) /
> [lean-proof-planning スキル](../../.github/skills/lean-proof-planning/SKILL.md) /
> [GitHub: leanprover-community/plausible](https://github.com/leanprover-community/plausible)

---

## 前提

- Plausible は Mathlib の推移的依存として**既に利用可能**（追加 `require` 不要）
- **S2IL REPL では `import Plausible` がデフォルト auto-import に含まれる**  
  `plausible` タクティクは追加 import なしでそのまま使える
- `-NoPickle` モードや S2IL と無関係のスタンドアロンファイルでは `import Plausible` が必要

---

## Plausible とは

`plausible` タクティク（旧: `slim_check`）は**プロパティベーステスト**を Lean の証明環境内で行うライブラリ。

- ランダムな入力値で命題を数十〜数百回テストし、**反例を探す**
- 反例が見つかればエラーとして報告（counterexample の値を表示）
- 反例が見つからなければ "Unable to find a counter-example" を出力し sorry を挿入
- **plausible は証明ではない**。「確認ツール」として使う

---

## 基本的な使い方

```lean
-- 真の命題: 反例が見つからない
example : ∀ n : Nat, n ≤ n + 1 := by plausible
-- → "Unable to find a counter-example" + sorry（警告あり）

-- 偽の命題: 反例が見つかる
example : ∀ n : Nat, n + 1 = n := by plausible
-- → error: Found a counter-example!
--   n := 0
--   issue: 1 = 0 does not hold
```

---

## 良い使い方 ✅

### 1. sorry 着手前の真偽チェック（最重要用途）

証明を始める前に、補題が本当に真かどうかを素早く確認する。

```lean
-- 証明作業前に REPL で実行して偽定理への投資を防ぐ
example : ∀ (s : Shape) (config : GameConfig),
    (s.gravity config).layers.length ≤ config.maxLayers := by plausible
```

### 2. 全称命題のサニティチェック

`∀` を含む命題でリファクタリング後に回帰確認する。

```lean
example : ∀ (q : Quarter), q.rotate180.rotate180 = q := by plausible
```

### 3. 具体値の `#eval` より手軽な全称チェック

具体値を手書きするよりも `plausible` の方が迅速に確認できる場合がある。

```lean
-- #eval で具体値を並べる代わりに
example : ∀ (d : Direction), d.rotate180.rotate180 = d := by plausible
```

---

## 悪い使い方 ❌

### 1. 「反例なし = 証明済み」として扱う

```lean
-- ❌ plausible は証明ではない
-- "Unable to find a counter-example" は「テストを通過した」だけ
-- 必ず最終的に sorry → 実際の証明タクティクに置換すること
theorem important_theorem : ... := by plausible  -- ❌ そのままリリースしない
```

### 2. `Arbitrary` / `SampleableExt` インスタンスのない型に使う

`plausible` はランダム値生成に `SampleableExt`（内部で `Arbitrary` + `Shrinkable`）型クラスを必要とする。
S2IL の主要型には `S2IL/Shape/Arbitrary.lean` で `SampleableExt` インスタンスが定義済みであり、
`import S2IL` でそのまま利用可能。

```lean
-- ✅ S2IL 型に対する plausible が使える
example : ∀ (c : Color), c.mix c = c := by plausible
example : ∀ (s : Shape), s.layers ≠ [] := by plausible
```

独自に定義した型に `plausible` を使う場合は `Arbitrary` + `Shrinkable` + `SampleableExt`
インスタンスが必要。`S2IL/Shape/Arbitrary.lean` の実装パターンを参考にすること。

### 3. 探索コストを考えずに複雑な命題に使う

`plausible` のランダム生成は基本的な命題では高速に動作するが、
計算量の多い関数（`gravity` 等）を含む命題ではテスト 1 件あたり数秒かかりうる。
通常の 100 回テストは数分以内に完了するが、タイムアウトの可能性に注意。

---

## REPL での使い方

```jsonl
{"cmd": "-- plausible タクティクは default env (import Plausible 済み) で即座に使える\nexample : ∀ n : Nat, n ≤ n + 1 := by plausible", "env": 0}
```

出力:
```json
{"messages":[{"severity":"info","data":"Unable to find a counter-example"},{"severity":"warning","data":"declaration uses `sorry`"}],"env":1}
```

偽命題の場合:
```json
{"messages":[{"severity":"error","data":"===================\nFound a counter-example!\nn := 0\nissue: 1 = 0 does not hold\n(0 shrinks)\n-------------------"}],"env":1}
```

---

## S2IL での現在の適用範囲

| 型 | `plausible` 対応 | 生成戦略 | 備考 |
|---|---|---|---|
| `Nat`, `Int`, `Bool` | ✅ | Lean 標準 | — |
| `Color` | ✅ | 8 バリアントから均一選択 | — |
| `PartCode` | ✅ | 6 バリアントから均一選択 | — |
| `RegularPartCode` | ✅ | 4 バリアントから均一選択 | — |
| `Direction` | ✅ | 4 バリアントから均一選択 | `decide` も利用可 |
| `Quarter` | ✅ | 4 種コンストラクタを均一選択 | — |
| `Layer` | ✅ | 4 象限を独立ランダム生成 | — |
| `Shape` | ✅ | 1～4 レイヤをランダム生成 | — |
| `QuarterPos` | ✅ | レイヤ (0～7) × 方角 | `decide` も利用可 |
| `GameConfig` | ✅ | maxLayers を 1～8 で生成 | — |
| `SettledShape` | ✅ | ランダム Shape に gravity 適用で安定化 | `SettledShape.lean` |

---

## `decide` との使い分け

| 観点 | `decide` | `plausible` |
|---|---|---|
| 型の要件 | `Decidable` | `Arbitrary` |
| 確実性 | **完全（全探索）** | ランダムサンプリング |
| 対象 | 有限型・小さい型 | `Nat`/`List Nat` 等の無限型 |
| 速度 | 型サイズに比例 | 設定した試行回数（デフォルト 100 回） |
| S2IL での優先度 | **Direction/QuarterPos 等は decide 優先** | Nat 等の無限型 |

**結論**: S2IL では有限型は `decide` が優先。S2IL 型を含む命題には `plausible` が利用可能
（`S2IL/Shape/Arbitrary.lean` で全主要型の `SampleableExt` インスタンスを定義済み）。

---

## Gotchas

- `plausible` が成功しても `sorry` 警告が出る。最終証明では必ず置換する
- 反例がなくても帰納的サイズの大きい問題（大きい `Nat` 値等）では反例を見逃す可能性がある
- S2IL 型のインスタンス定義は `S2IL/Shape/Arbitrary.lean` に集約されている。新しい型を追加した場合はこのファイルにインスタンスを追加すること
- `Shape` の生成は 1～4 レイヤ。5 レイヤ以上の特殊ケースをテストしたい場合は `#eval` で具体値を作成する
