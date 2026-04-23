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

## `_agent/` — エージェント向けインデックス

`S2IL/_agent/` には 4 つのインデックスがある。作業開始時に必要なものを参照すること。

| ファイル | 用途 | 使い方 |
|---|---|---|
| `symbol-map.jsonl` | シンボル名 → ファイル・種別・タグ | `grep_search` の**前に**ここを検索。public 宣言のみ収録 |
| `route-map.json` | 操作モジュールの読み込み順序 | 新しいモジュールを探索する際の出発点 |
| `query-playbook.json` | タスク別探索レシピ | `equivariance_add` / `sorry_settle` / `symbol_lookup` 等の手順書 |
| `dep-graph-baseline.json` | モジュール依存グラフ | 影響範囲調査・ビルド順序の確認 |

### 使用手順

**シンボル検索**（最優先）:
```
grep_search pattern="\"symbol\": \"waveStep\"" includePattern="S2IL/_agent/symbol-map.jsonl"
```
→ ファイルパスが判明したら直接 `read_file`。`grep_search` でコードを広範囲検索する前に必ず試す。

**タスク別レシピ**:
- sorry 解消 → `query-playbook.json` の `sorry_settle` レシピを確認
- 等変性追加 → `equivariance_add` レシピを確認
- モジュール探索 → `route-map.json` の `routes.{操作名}` を確認

> インデックスは Stop フック（`regen-indices.ps1`）でビルド成功時に自動再生成される。

## 大ファイル探索の制限

- **CommExt 系サブファイル**（FloatUnits / LandingDist / PlaceGrounding / CommNe / SortStability）を `read_file` するときは、同一ファイルへの 2 回目以降の読み込み前に `/memories/session/` に行番号マップを記録する。
- 同一ファイルへの `read_file` が 3 回目になったら即座に `Explore` サブエージェントに委譲すること。
  - 委譲テンプレート: `runSubagent Explore "CommExt/{FileName}.lean の L{X}〜L{Y} 付近で {目的} を探して"`

## 構造リファクタ提案の形式

- sorry の増加を伴う構造リファクタを提案するときは、以下の数値を先にユーザーへ提示する:
  - 今セッションで削減可能な sorry 数（見積もり）
  - 次セッション以降で削減予定の sorry 数
  - sorry 増加後の全体 sorry 数

## 一時ファイル

- 実験は `Scratch/` を使い、トップレベルに一時ファイルを置かない
- JSONL 運用は `../Scratch/AGENTS.md` を参照
