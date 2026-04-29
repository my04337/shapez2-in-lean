---
name: lean-proof-planning
description: >
  Pre-proof checklist and decision guide that prevents investing in false theorems.
  Use when: prove theorem, proof strategy, settle sorry, plan proof, stuck on proof,
  start proof, proof approach, verify lemma truth, false theorem check,
  switch proof approach, new proof strategy, after false lemma discovery,
  証明戦略, 証明計画, 証明着手前チェック, 偽定理回避.
  Returns: pre-flight checklist + branching decision tree.
  Don't call when: you only need to run the checks (delegate to agent `lean-sorry-investigator`).
metadata:
  argument-hint: 'Reference: pre-proof planning checklist'
---

# 証明戦略スキル

**書く前に確かめる**。偽定理への投資を避け、着手判断を反例検証ベースで行う。

## チェックリスト

### 補題の真偽ゲート（着手前）

- [ ] 型シグネチャ（量化変数・仮定・結論・暗黙引数）を正確に読んだ
- [ ] 反例チェックを実施: `lean-sorry-investigator` エージェント / REPL `by plausible` / `#eval decide`
  - 基本型の全称命題は `by plausible` が最速
  - S2IL 型（`Color`, `Quarter`, `Layer`, `Shape`, `Direction`, `QuarterPos`, `GameConfig` 等）も `SampleableExt` 定義済みで `plausible` 可
  - 層数指針は `lean-counterexample` スキル参照（vanilla4 デフォルト、vanilla5 最終確認）
- [ ] 使用予定補題の仮定が今回の文脈で成立するか確認
- [ ] 代替補題への乗り換え時、循環依存（代替補題の条件 = 元のゴール）でないか 1〜2 ステップで確認

**反例が見つかった場合**: 計画を即中止し、仮定追加・結論弱化・スコープ限定でシグネチャを修正してから再検証する。

### sorry 分解と個別検証

- [ ] sorry 骨格で先に書き、各 sorry を独立した証明義務に分解する
- [ ] 証明木の深さ 3 レベル以内を目標にする（深い `have` ネストは独立補題に分離）
- [ ] 各 sorry に反例チェックを実施（1 つでも偽なら分解を見直す）
  - REPL でゴール確認:
    ```jsonl
    {"cmd": "theorem target ... := by\n  intro h\n  sorry", "env": 0}
    {"tactic": "simp", "proofState": 0}
    ```
- [ ] 各 sorry に非形式スケッチ（1〜2 行の方針）を記録
- [ ] 推定行数・難易度・撤退条件を記録（例: 100 行超で再検討）

### 実装中

- [ ] 50 行ごとにビルドして sorry 数を監視
- [ ] ビルドエラー多発時は **最内側** から 1 箇所ずつ sorry 化して再ビルド（Mechanic Sorrifier）
- [ ] 撤退シグナル: 同一戦略 200 行で進展なし / 新 sorry 3 つ以上 / 仮定追加が止まらない
- [ ] 同一 sorry に 8 アプローチ以上失敗 → `lean-proof-progress` スキルで正式撤退判断

## ゴール形状 → ファーストアクション

| ゴール形状 | 第1候補 | 第2候補 | 代替 |
|---|---|---|---|
| `⊢ a = b`（環上） | `ring` | `simp only [...]` | `calc` |
| `⊢ a = b`（Nat/Int 線形） | `omega` | `norm_num` | `rw [lemma]` |
| `⊢ a < b` / `⊢ a ≤ b`（Nat/Int） | `omega` | `linarith` | `norm_num` |
| `⊢ ∀ x, P x` / `⊢ A → B` | `intro` | `rintro` | — |
| `⊢ ∃ x, P x` | `use witness` | `refine ⟨?_, ?_⟩` | — |
| `⊢ A ∧ B` | `constructor` | `exact ⟨_, _⟩` | — |
| `⊢ A ∨ B` | `left` / `right` | `by_cases` | — |
| 帰納型 | `cases x` | `induction x` | `rcases` |
| 仮定に一致候補あり | `exact h` | `apply h` | `assumption` |
| `⊢ False` / 矛盾仮定 | `contradiction` | `omega` | `simp_all` |
| 有限列挙型 | `decide` | `cases <;> decide` | — |
| キャスト混在 | `norm_cast` | `push_cast` → `ring` | `zify` |
| `⊢ f = g`（関数等式） | `funext` | `ext` | — |
| 不明 | `exact?` | `aesop` / `duper [*]` / `grind` | 一時 `sorry` |

- `exact?` / `apply?` で見つからない場合は `lean-mathlib-search` スキル
- `aesop` は構造的ゴールに有効。成功時は `aesop?` で安定化
- `duper [*]` は一階述語論理の推論に強い。成功時は `duper?` で安定化
- 詳細: [`docs/lean/aesop-guide.md`](../../../docs/lean/aesop-guide.md), [`docs/lean/duper-guide.md`](../../../docs/lean/duper-guide.md)

## 偽定理のシグナル

- `cases` で到達不能ケースが証明できない
- 仮定を次々追加しないと進まない
- `exact?` / `apply?` が何も見つけない
- ペアワイズ条件で N 要素の性質を主張（3-cycle が潜む）
- グリーディアルゴリズムで第三者の影響を無視

## 既知の偽定理パターン

| パターン | 偽の本質 |
|---|---|
| グリーディソートが topological sort を生成 | insertSorted の貪欲停止が順序を壊す |
| 2-cycle 禁止 → DAG | 3-cycle が存在し得る |
| foldl settle が置換不変 | 方角列共有ペアが順序依存 |
| ソート位置がランク関数 | 入力順序依存で位置が変わる |

## Gotchas

- sorry を含む定理で別の定理を証明すると偽の安心感を生む → sorry 連鎖は最小限に
- `#eval` は計算可能な式のみ。`Prop` は `decide` で
- 反例なし ≠ 証明の存在。あくまでリスク軽減策

## 関連

- **lean-counterexample** / **lean-proof-progress** スキル
- **lean-sorry-investigator** エージェント（1 件の sorry / 仮定理に対する反例チェック + タクティク試行 + 補題探索の一括調査）

### Duper 試行フロー

1. sorry のゴールを REPL で確認（env: 0 で利用可能）
2. `duper? [*]` を試行（~15s）
3. 成功 → portfolioInstance 付きに安定化
4. 失敗 → ファクト選別 `duper [h1, h2, external_lemma]`
5. それでも失敗 → `induction` / `cases` / `simp` 等へ切替

詳細: [`docs/lean/duper-guide.md`](../../../docs/lean/duper-guide.md)
