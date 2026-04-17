---
name: lean-proof-planning
description: >
  Plan and pre-validate Lean 4 proof strategy before starting; prevents false-theorem waste.
  Use when: prove theorem, proof strategy, settle sorry, plan proof, stuck on proof,
  start proof, proof approach, verify lemma truth, false theorem check,
  switch proof approach, new proof strategy, proof approach change, after false lemma discovery.
metadata:
  argument-hint: 'Pass theorem signature or describe the proof goal'
---

# 証明戦略スキル

**書く前に確かめる**。偽定理に数百行費やす事態を段階的ゲートで回避する。

## Phase 0（必須・先行実行）: 補題の真偽ゲート

> **このスキルを読んだ直後、証明計画を立てる前に必ず実行する。**

1. **`lean-theorem-checker` エージェントを呼び出す**（または REPL `#eval` / `by plausible` で具体値 1-2 個を確認）
   - `Nat` / `Bool` 等の基本型の全称命題は `by plausible` が迅速（REPL default で import 不要）
   - S2IL 型（`Color`, `Quarter`, `Layer`, `Shape`, `Direction`, `QuarterPos`, `GameConfig` 等）も `by plausible` で利用可能（`SampleableExt` インスタンス定義済み）
2. エージェントが **「FALSE with counterexample」** を返した場合（または `plausible` が "Found a counter-example!" を出力した場合）:
   - 証明計画・アプローチ検討は**即座に中止**する
   - 補題のシグネチャ修正（仮定追加・結論弱化・スコープ限定）を先行する
   - 修正後のシグネチャで再度 Phase 0 を実行する
3. **「TRUE」** が確認されてからゲート 1 へ進む

**禁止**: Phase 0 を省略してコード読解・アプローチ検討を始めること。
「おそらく真だろう」という推測でスキップしても可換ではない（実績: 任意 obs で偽の補題に 5 ブロック分のインライン推論を費やした事例あり）。

---

## ゲート 1: 定理の真偽確認

1. **型シグネチャを正確に読む**: 量化変数・仮定・結論・暗黙の引数まで確認
2. **反例チェック（必須）**: デフォルト vanilla4 (4L) で具体値 + 境界値・退化ケース。最終確認は vanilla5 (5L)
   - `lean-theorem-checker` エージェントで自動化可能
   - 層数指針は **lean-counterexample** スキルの「GameConfig 層数の指針」を参照
3. **依存補題の健全性**: 使用予定の補題の仮定が今回の文脈で成立するか確認
   - **代替補題への乗り換え時は循環依存を先読みする**: 代替補題の h 条件が元のゴールと同義でないかを 1〜2 ステップで確認してから分析に入ること。詳細な実装読み・REPL 検証を行う前に「条件の充足に元のゴールが必要になる循環でないか」を検討する

→ 反例あり: 仮定追加 / 結論弱化 / 撤回を検討
→ 反例なし: ゲート 2 へ

## ゲート 2: sorry 分解と個別検証

4. **sorry で骨格を先に書く**: 各 sorry を独立した小さな証明義務に分解
   - **証明木は「浅く広く」** を設計目標にする。deeper than 3 levels のネスト（`have` の中に `have` の中に `have`...）を避け、可能なら独立した補題に分離する。（→ ビルド時間短縮 + sorry 個別解消の並列化）
   - **Mechanic Sorrifier パターン**: ビルドエラーが多数出た場合、**最内側の `have` ブロック**から 1 箇所ずつ sorry 化して再ビルドする。1 置換ごとに再コンパイルし、カスケードエラーを除去してから取り組む
5. **各 sorry の非形式スケッチ（推奨）**: 各 sorry に対して自然言語で 1〜2 行の証明方針を `/memories/session/` またはコード中コメントに記録してからタクティクに取り掛かる。方向性の迷走を防ぐ
6. **各 sorry の反例チェック（必須）**: 偽の sorry が **1 つでもあれば**戦略再検討。分解直後に全サブゴールを一括チェックする
   - `lean-theorem-checker` エージェントまたは REPL `by plausible` で各サブゴールを個別に検証する
   - REPL で sorry のゴールを直接確認可能:
     ```jsonl
     {"cmd": "theorem target ... := by\n  intro h\n  sorry", "env": 0}
     {"tactic": "simp", "proofState": 0}
     ```
7. **見積もり記録**: 推定行数・難易度・撤退条件（例: 100行超で再検討）

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
| 不明 | `exact?` | `aesop` / `duper [*]` / `grind` | `sorry` で一時スキップ |

> `exact?` / `apply?` で見つからない場合は **lean-mathlib-search** スキル（`#leansearch` / `#loogle` を含む段階的検索）を参照。
>
> `aesop` は `simp` で閉じない構造的ゴールに有効。成功時は `aesop?` で安定版を取得する。詳細: [`docs/lean/aesop-guide.md`](../../../docs/lean/aesop-guide.md)
>
> `duper [*]` は一階述語論理の推論チェーン（`∀`, `∃`, `→`, `∧`, `∨`）に強い。成功時は `duper?` で `portfolioInstance` を取得し安定化する。帰納法・高階関数・算術には向かない。詳細: [`docs/lean/duper-guide.md`](../../../docs/lean/duper-guide.md)

## ゲート 3: 実装中の定期確認

8. **50 行ごとにビルド**: sorry 数増加を監視
   - ビルドエラー発生時は **Sorrifier パターン** を適用: 最内側エラーから 1 箇所ずつ sorry 化 → 再ビルド → カスケード除去
9. **撤退判断**: 同一戦略 200 行で進展なし / 新 sorry 3 つ以上 / 仮定追加が止まらない
10. **撤退ゲート（アプローチ 8 回失敗）**: 同一 sorry に対してアプローチが累計 8 回以上失敗した場合、**`lean-proof-progress` スキルをロードして正式撤退判断を実行する**。残り時間はドキュメント更新・次 sorry の分析に充てること

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
- [ ] sorry 骨格に分解し、**各 sorry の反例チェック**を実施した（サブゴール単位で個別検証）
- [ ] sorry を配置した補題の **上流依存先**（その sorry に依存する定理チェーン）を把握・記録した
- [ ] 証明見積もり（推定行数・難易度・撤退条件）を記録した
- [ ] 証明木の深さが 3 レベル以内であることを確認した（深い場合は独立補題に分離）
- [ ] 各 sorry に対する非形式スケッチ（1〜2 行の方針メモ）を記録した

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

**lean-counterexample** / **lean-proof-progress** / **lean-theorem-checker** エージェント

**行き詰まり時の Duper 試行フロー**:

```
1. sorry のゴールを REPL で確認（env: 0 で duper 即利用可能）
2. duper? [*] を試行（~15s）
3. 成功 → portfolioInstance 付きに安定化
4. 失敗 → ファクトを選別して duper [h1, h2, external_lemma] を試行
5. それでも失敗 → 別のアプローチ（induction, cases, simp 等）に切り替え
```

詳細: [`docs/lean/duper-guide.md`](../../../docs/lean/duper-guide.md)
