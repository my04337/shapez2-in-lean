---
name: lean-proof-planning
description: >
  Lean 4 の定理証明作業を開始する前に、証明戦略の事前検証と反例チェックを行う。
  偽定理への時間浪費を防ぎ、段階的なゲート判断で証明作業を効率化する。
  Use when: prove theorem, proof strategy, settle sorry, plan proof, stuck on proof,
  start proof, proof approach, verify lemma truth, false theorem check.
metadata:
  argument-hint: '証明戦略の立案と事前検証を行います'
---

# 証明戦略スキル

**書く前に確かめる**。偽定理に数百行費やす事態を段階的ゲートで回避する。

## ゲート 1: 定理の真偽確認

1. **型シグネチャを正確に読む**: 量化変数・仮定・結論・暗黙の引数まで確認
2. **反例チェック（必須）**: デフォルト vanilla4 (4L) で具体値 + 境界値・退化ケース。最終確認は vanilla5 (5L)
   - `lean-theorem-checker` サブエージェントで自動化可能
   - 層数指針は **lean-counterexample** スキルの「GameConfig 層数の指針」を参照
3. **依存補題の健全性**: 使用予定の補題の仮定が今回の文脈で成立するか確認

→ 反例あり: 仮定追加 / 結論弱化 / 撤回を検討
→ 反例なし: ゲート 2 へ

## ゲート 2: sorry 分解と個別検証

4. **sorry で骨格を先に書く**: 各 sorry を独立した小さな証明義務に分解
5. **各 sorry の反例チェック**: 偽の sorry が 1 つでもあれば戦略再検討
   - REPL で sorry のゴールを直接確認可能:
     ```jsonl
     {"cmd": "theorem target ... := by\n  intro h\n  sorry", "env": 0}
     {"tactic": "simp", "proofState": 0}
     ```
6. **見積もり記録**: 推定行数・難易度・撤退条件（例: 100行超で再検討）

→ 全 sorry 通過: 実装着手
→ 偽 sorry 発見: 分解の見直し

## ゴール形状 → ファーストアクション（クイックリファレンス）

sorry を分解した各ゴールに対して、最初に試すべきタクティクの早見表。
詳細は **lean-tactic-select** スキルおよび `docs/lean/tactics/index.md` を参照。

| ゴール形状 | 第1候補 | 第2候補 | 代替 |
|---|---|---|---|
| `⊢ a = b`（環上） | `ring` | `simp only [...]` | `calc` で段階証明 |
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
| 不明 | `exact?` | `aesop` / `grind` | `sorry` で一時スキップ |

> `exact?` / `apply?` で見つからない場合は **lean-mathlib-search** スキル（`#leansearch` / `#loogle` を含む段階的検索）を参照。

## ゲート 3: 実装中の定期確認

7. **50 行ごとにビルド**: sorry 数増加を監視
8. **撤退判断**: 同一戦略 200 行で進展なし / 新 sorry 3 つ以上 / 仮定追加が止まらない

## 偽定理のシグナル

- `cases` で到達不能ケースが証明できない
- 仮定を次々追加しないと進まない
- `exact?` / `apply?` が何も見つけない
- ペアワイズ条件で N 要素の性質を主張（3-cycle が潜む）
- グリーディアルゴリズムの不変条件で第三者の影響を無視

## 既知の偽定理パターン

| パターン | 偽の本質 |
|---|---|
| グリーディソートが topological sort を生成 | insertSorted の貪欲停止が順序を壊す |
| 2-cycle 禁止 → DAG | 3-cycle が存在し得る |
| foldl settle が置換不変 | 方角列共有ペアが順序依存 |
| BFS 列挙がリスト等号で変換等変 | 探索順序が変換で変わる |
| ソート位置がランク関数 | 入力順序依存で位置が変わる |

## 早期検出チェックリスト

- [ ] 量化変数・仮定・結論・暗黙引数まで型シグネチャを正確に読んだ
- [ ] デフォルト 4L + 境界値（空・singleton・退化ケース）で反例がないことを確認した
- [ ] 有限型は `by decide` または REPL `#eval decide (...)` で全探索した
- [ ] 使用する補題の仮定が今回の文脈で成立することを確認した
- [ ] sorry 骨格に分解し、各 sorry の反例チェックを実施した
- [ ] sorry を配置した補題の **上流依存先**（その sorry に依存する定理チェーン）を把握・記録した
- [ ] 証明見積もり（推定行数・難易度・撤退条件）を記録した

| # | チェック |
|---|---|
| 1 | 2 要素の具体値テスト |
| 2 | 3 要素テスト（順序入替） |
| 3 | BFS 結果をリスト等号で比較していないか |
| 4 | foldl で置換不変性を仮定していないか |
| 5 | 二項関係から全順序・DAG を自動導出していないか |
| 6 | 補題の仮定が文脈で過不足なく成立するか |
| 7 | ソート位置をランク関数に使っていないか |
| 8 | sorry の偽判定が発覚した場合の影響範囲（上流チェーン）を文書化したか |

## Gotchas

- sorry を含む定理で別の定理を証明すると**偽の安心感**を生む。sorry 連鎖は最小限に
- `#eval` は計算可能な式のみ。`Prop` → `decide` を使う
- 反例なし ≠ 証明の存在。あくまでリスク軽減策

## 関連

**lean-counterexample** / **lean-proof-progress** / **lean-theorem-checker** サブエージェント
