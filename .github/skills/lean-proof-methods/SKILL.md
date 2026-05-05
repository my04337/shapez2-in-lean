---
name: lean-proof-methods
description: >
  Reference hub for Lean proof methods: counterexample checks, goal-shape tactic selection, Mathlib/Batteries lemma search, proof planning, and retreat/pivot criteria. Use when: prove theorem, proof strategy, counterexample, plausible, tactic selection, exact?, apply?, simp?, leansearch, loogle, proof stuck, pivot, 証明戦略, 反例, 補題探索, タクティク選択, 撤退判断. Returns: method selection guide + links to detailed catalogs. Don't call when: you want the checks or tactics actually executed; use agent `lean-theorem-investigator`.
---

# Lean Proof Methods

Lean 証明作業の参照入口。反例・タクティク選択・補題探索・証明計画・進捗管理の詳細資料は `references/` に移し、active skill はこの 1 本に集約する。

## 最初の分岐

| 状況 | 次に見るもの |
|---|---|
| 候補 theorem / 補題が真か不安 | 反例チェック catalog |
| ゴール形状は分かるが tactic が不明 | tactic priority map |
| tactic だけでは進まない | lemma search patterns |
| 複数補題・分解方針が必要 | proof planning checklist |
| 何度も失敗している | retreat / pivot criteria |
| 実行まで任せたい | `lean-theorem-investigator` |

## 標準フロー

1. 新規補題・仮説は、証明本文を書く前に具体値検証する。
2. REPL で `example ... := by sorry` を通し、ゴール形状を確定する。
3. goal shape に応じた tactic を 1〜数個試す。
4. tactic が進まない場合のみ `exact?` / `apply?` / `simp?` / `#leansearch` / `#loogle` へ進む。
5. 反例・全滅・長期停滞が確認できたら statement 修正または pivot を検討する。

## Agent との境界

| やりたいこと | 推奨 |
|---|---|
| 方針表や既知パターンを読む | この skill |
| theorem 1 件の反例チェックから tactic 試行まで任せる | `lean-theorem-investigator` |
| 複数 theorem / 複数 sorry の並列 triage | `lean-theorem-investigator` を fan-out |
| build failure の原因分類 | `lean-build-doctor` |
| `simp only` への機械的安定化 | `lean-simp-stabilizer` または `lean-simp-guide` |

## 詳細参照

| 参照 | 役割 |
|---|---|
| [`references/counterexample.md`](references/counterexample.md) | 境界値・相互作用・GameConfig tier |
| [`references/tactic-select.md`](references/tactic-select.md) | ゴール形状 → tactic 優先マップ |
| [`references/mathlib-search.md`](references/mathlib-search.md) | `exact?` / `apply?` / `#leansearch` / `#loogle` |
| [`references/proof-planning.md`](references/proof-planning.md) | 着手前 checklist と偽定理回避 |
| [`references/proof-progress.md`](references/proof-progress.md) | 長期進捗・撤退判断 |
