---
name: s2il-proof-workflow
description: >
  S2IL-specific proof workflow reference: facade-first search, Layer A/B architecture, Prop/Bool bridge pattern, theoremization flow, validation targets, and documentation ownership. Use when: S2IL proof work, Shapez2 theorem, facade search, Prop Bool bridge, Layer A/B, validation, theoremization, S2IL 証明, theorem 化, 仕様照合, ドキュメント更新. Returns: project-specific workflow checkpoints + canonical docs. Don't call when: the task is generic Lean tooling or Mathlib lemma search; use `lean-tooling` or `lean-proof-methods`.
---

# S2IL Proof Workflow

S2IL 固有の証明・検証・ドキュメント運用の active skill。Lean 一般の方法論は `lean-proof-methods`、コマンド実行は `lean-tooling` を参照する。

## 入口

| 領域 | 正本 |
|---|---|
| S2IL アーキテクチャ | [`docs/s2il/architecture-layer-ab.md`](../../../docs/s2il/architecture-layer-ab.md) |
| S2IL コードベース | [`docs/s2il/README.md`](../../../docs/s2il/README.md) |
| Shapez2 仕様 | [`docs/shapez2/README.md`](../../../docs/shapez2/README.md) |
| 計画 / マイルストーン | [`docs/plans/README.md`](../../../docs/plans/README.md) |
| エージェント運用 | [`docs/agent/README.md`](../../../docs/agent/README.md) |

## Facade-first 探索

Lean シンボル探索は facade の冒頭目次から始める。

| 目的 | 入口 |
|---|---|
| 全体 facade | `S2IL.lean` |
| Shape | `S2IL/Shape.lean` |
| Kernel | `S2IL/Kernel.lean` |
| Operations | `S2IL/Operations.lean` |
| Wires / Machine | `S2IL/Wires.lean`, `S2IL/Machine.lean` |

facade で見つからない場合のみ対象 namespace に絞って `grep_search` する。横断要約が必要なら `Explore` に委譲する。

## 証明スタイル

- Prop primitive / Bool via `decide` / bridge theorem `.iff` を基本形にする。
- 回転等変性は CW を主鎖にし、180° / CCW は既存の 1 行系で導く。
- 公開 theorem の追加前に REPL `#check` / `example ... := by sorry` で型を確認する。
- 新規補題・仮説は `lean-proof-methods` の反例チェックを通す。
- 実行や REPL の手順は `lean-tooling` を正本にする。

## Validation

| 対象 | 標準確認 |
|---|---|
| 既定ライブラリ | `.github/skills/lean-tooling/scripts/build.ps1` |
| Test ライブラリ | `.github/skills/lean-tooling/scripts/build.ps1 -Target Test` |
| Gravity 公開 theorem | `Test.Operations.GravityValidation` / `Test` target |
| 文書移動・削除 | 旧パス・旧文言を `grep_search` で確認 |

## Agent との境界

| 状況 | 委譲先 |
|---|---|
| build / diagnostics の正本確認 | `lean-build-doctor` |
| theorem 候補の真偽・挙動・tactic triage | `lean-theorem-investigator` |
| session 再開 / compact 後の現状復元 | `lean-session-restorer` |
| 1 行の `simp` 安定化 | `lean-simp-stabilizer` |

## ドキュメント所有権

重複転記を避ける。仕様は `docs/shapez2`、S2IL 設計は `docs/s2il`、進捗と計画は `docs/plans`、運用は `docs/agent` を正本にする。
