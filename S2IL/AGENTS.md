# S2IL Lean コーディング規約（簡約版）

> `S2IL/` 配下ではこの規約を適用する。全体規約は `../AGENTS.md` を参照。

## 命名規則（要点）

- public 定義は可読性優先で、意味が分かる長めの名前を使う
- 1〜2 文字の短縮名を public で使わない
- 変数慣例: `s`（Shape）, `l`（Layer）, `q`（Quarter）, `p`（QuarterPos）, `config`（GameConfig）

詳細: `../docs/lean/naming-conventions.md`

## API と名前空間

- 実装は操作別 namespace（例: `Gravity`, `PinPusher`）に置く
- 公開 API は `Shape` namespace 拡張で提供する
- `open` は必要名のみを選択的に使う

## 補題の配置ルール（bridge / helper）

- **汎用 bridge 補題**（例: `isOccupied ↔ getDir`, `getQuarter ↔ layers.getD`）は操作固有ファイル（`Operations/Gravity/**`）に置かない
  - 基本原則: 補題が参照する最上流シンボルの定義元ファイル、またはその 1 つ下流に置く
  - 例: `isOccupied_of_getDir_ne_empty` は `Defs.lean` の `isOccupied` 定義直後が正しい
- 操作固有の補題（`placeFallingUnit`, `placeLDGroups` など）はその操作のサブモジュール内に留める
- 配置判定が迷う場合は `docs/plans/MILESTONES.md` フェーズ R の R-2 に「後で移動」として TODO 登録する

詳細な整理計画: `docs/plans/MILESTONES.md` フェーズ R-2

## ドキュメントコメント

- public `def` / `theorem` には日本語 `/-- ... -/` を必須とする

## 証明スタイル

- 最終形は `simp only [...]` を使う（裸 `simp` を残さない）
## 証明ワークフロー（要点）

- Proof-First-Test: 証明前に `lean-theorem-checker` または REPL で真偽確認
- 3 アプローチ以上の推論停滞時は REPL / Scratch 検証へ切り替える
- 長大ファイルの探索は Explore でバッチ取得してから着手する

詳細: `../docs/s2il/proof-workflow-playbook.md`

## REPL 優先

- タクティク変更・新規 API・`simp only` 置換前は REPL で即時検証
- 200 行以上の挿入は段階的に REPL 検証してから反映する
- **必須**: 新規 `sorry` を .lean ファイルに書き込む前に REPL で `example ... := by sorry` を実行してゴール形状を確認する。確認なしで sorry を書くことは禁止。

## 補題探索

1. REPL `#check @候補名`
2. `lean-mathlib-search` スキル
3. Explore で mathlib ソース検索
4. 最後に build

## `_agent/` — 証明進捗ノート

Phase A (2026-04-24) でインデックス機構（symbol-map / route-map / query-playbook / dep-graph-baseline / sig-digest）は廃止された。
残存するのは **証明進捗ノート** のみ:

| ファイル | 用途 |
|---|---|
| `sorry-plan.json` | アクティブな sorry / axiom のスナップショット |
| `sorry-goals.md` | sorry 位置の宣言シグネチャ一覧（ビルド時に自動生成） |
| `sorry-cards/*.md` | 個別 sorry の作業ノート（手動メンテ）|

シンボル検索は facade（`S2IL/<Namespace>.lean`）の冒頭目次を読んでから `grep_search` を使う。
インデックスに相当する機構は Phase E 以降もあえて復活させない（[architecture-layer-ab.md §1.7](../docs/plans/architecture-layer-ab.md)）。

## 大ファイル探索の制限

- 200 行超のファイルを `read_file` するときは、該当 namespace の facade (`S2IL/<Namespace>.lean`) の冒頭目次を先に読むこと。
- 同一ファイルへの `read_file` が 3 回目になったら即座に `Explore` サブエージェントに委譲すること。
  - 委譲テンプレート: `runSubagent Explore "{File}.lean の L{X}〜L{Y} 付近で {目的} を探して"`

## 構造リファクタ提案の形式

- sorry の増加を伴う構造リファクタを提案するときは、以下の数値を先にユーザーへ提示する:
  - 今セッションで削減可能な sorry 数（見積もり）
  - 次セッション以降で削減予定の sorry 数
  - sorry 増加後の全体 sorry 数

## 一時ファイル

- 実験は `Scratch/` を使い、トップレベルに一時ファイルを置かない
- JSONL 運用は `../Scratch/AGENTS.md` を参照
