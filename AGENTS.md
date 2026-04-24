# Shapez2 in Lean — エージェント運用指示

## 応答と日時

- 最終応答は日本語。サブエージェント指示は英語可
- 日付 `YYYY-MM-DD` / 時刻 `hh:mm:ss`。当日日付が不明なら `Get-Date -Format 'yyyy-MM-dd'` で確認
- `作成日` / `最終更新` は当日ローカル日付を使う

## 参照入口

作業開始時、対象カテゴリの README を最初に読む。

- shapez2: `docs/shapez2/README.md`
- lean: `docs/lean/README.md`
- s2il: `docs/s2il/README.md`
- plans: `docs/plans/README.md`
- agent: `docs/agent/README.md`

新規証明計画の策定は `docs/agent/proof-plan-current-focus-guide.md` に従う。
撤退・pivot 判断は `docs/agent/proof-retreat-pivot-guide.md` に従う。

## 品質優先順位

1. 数学的な美しさ（構造・一般性・MECE: 補題が漏れなくダブりなく設計されているか）
2. コードの美しさ（可読性・保守性）

## 情報探索の優先順位

インデックス機構（symbol-map / sig-digest / route-map / query-playbook / dep-graph-baseline）は Phase A (2026-04-24) で廃止された。
エージェントは **facade を出発点** に、最短経路で目的のコードへ到達する。

次の順で探し、前段で見つかったら後段には進まない:

| # | 目的 | 参照先 |
|---|---|---|
| 1 | モジュールの入口 | 対応する facade (`S2IL.lean` / `S2IL/<Namespace>.lean`) の冒頭目次コメント |
| 2 | シンボル名で位置特定 | `grep_search` でシンボル名を検索（対象は `S2IL/**/*.lean`、`_archive/` は除外） |
| 3 | sorry 状況 | `S2IL/_agent/sorry-plan.json` → `S2IL/_agent/sorry-goals.md` → `S2IL/_agent/sorry-cards/{symbol}.md` |
| 4 | sorry 周辺のゴール形状 | REPL で `example ... := by sorry` を発行 |
| 5 | それでも不足 | Lean ソースへ広めに `grep_search` |

構造の正本は [docs/plans/architecture-layer-ab.md](docs/plans/architecture-layer-ab.md)、
Phase 別の実施計画は [docs/plans/layer-ab-rewrite-plan.md](docs/plans/layer-ab-rewrite-plan.md) を参照。

Lean では `semantic_search` を使わない。検索系は `grep_search` / `file_search` を優先。
`grep_search` が `No matches found` のときは `includeIgnoredFiles: true` で 1 回だけ再試行する。
`_archive/pre-greenfield/` 配下は旧実装の退避領域であり、明示指示がない限り `read_file` しない。

### preflight チェックリスト

`.lean` ファイルを `read_file` する直前に次を確認する:

- [ ] 該当 namespace の facade 冒頭目次を先に読んだか
- [ ] sorry 周辺なら REPL で `example ... := by sorry` のゴール形状を先に確認したか
- [ ] 会話要約継続セッションで、対象 sorry の「ファイル:行 / コード状態 / 次アクション / ビルド状態」が summary に揃っていればスキップ可

## セッションメモリ

- 原則 2 ファイル以内（断片化禁止）
- 次の状況で必ず `/memories/session/` を更新:
  - 異なる `.lean` ファイルを 3 本以上 read した
  - セッションターン数が 30 を超えた
  - 同じ sorry について 2 ラウンド以上 tactic を試した
- 要約は「現在の目的・読んだファイルと要点・次アクション」の 3 項目のみ
- 更新は `str_replace` / `insert` を使う。`delete → create` サイクルは禁止

詳細テンプレート: `docs/agent/session-memory-guide.md`

## ドキュメント管理（シングルソース原則）

| 情報 | 正規の場所 | 禁止事項 |
|---|---|---|
| ビルド状態・sorry 件数 | `sorry-goals.md`（自動生成） | 計画 MD への手動転記 |
| 次アクション・手順・フォローアップ | `sorry-plan.json` の `next_actions` / `remaining_steps` | sorry-card への重複記載 |
| 実装設計（シグネチャ候補・不変量・依存） | `sorry-cards/{symbol}.md` の実装設計セクション | sorry-plan.json への数学的詳細 |
| sorry 依存・blockers | `sorry-plan.json` | proof-plan.md への併記 |
| セッション経緯・発見 | `git log` | 計画 MD への時系列追記 |
| 数学的設計・記号定義 | `docs/plans/{name}-proof-plan.md` | sorry-card への重複 |

新規ドキュメント作成前に「自動更新されるか／既存で代替できるか」を確認する。
自動生成と 50% 以上重複する、または 2 セッション以上更新されていないドキュメントは `archive/` へ移す。

## 証明作業

- 新規補題・仮説は証明前に反例検証を優先（`lean-counterexample` / `by plausible` / `#eval`）
- 既存 sorry の状態確認は `sorry-plan.json` → `sorry-goals.md` → 当該 sorry-card の順
- 完了済み補題は本文を読まず REPL `#check` で型だけ確認
- 新規 `theorem` / `lemma` を書き込む前に REPL の `#check` / `example ... := by sorry` で型シグネチャを確認する
- 新規補題名は REPL 型チェック通過後に確定する（仮称を sorry-card / sorry-plan.json に書かない）
- REPL → `.lean` 移植は `transplant-proof.ps1` を使う（bare `simp` は `-SimpStabilize`）
- `intro` / `rintro` を書く前に REPL で sorry ゴール形状を確認する

### 行き詰まったときの必須フロー

「推論で難しそう」だけで撤退しない。次を順に実施してから pivot を判断する:

1. `lean-proof-planning` SKILL を読む
2. REPL で `example ... := by sorry` を発行してゴール形状を確認
3. `lean-goal-advisor` エージェントに渡して候補タクティクを試す

3 ステップ実施後に候補が全滅、反例が見つかった、または 3 セッション / 8 アプローチ失敗に達した場合にのみ撤退判断を行う。
詳細: `docs/agent/proof-retreat-pivot-guide.md`

### sorry-cards の更新

証明済みになった補題・`next_actions` の変化・セッション末コミット前に必ず更新する。
更新は差分のみを `replace_string_in_file` で行う。

## Lean ビルド

- `.github/skills/lean-build/scripts/build.ps1` を使う（VS Code task の直接実行よりスキル経由を優先）
- ビルド成功時に次が自動生成される:

| 生成物 | 用途 |
|---|---|
| `S2IL/_agent/sorry-goals.md` | sorry 宣言シグネチャ一覧 |

`symbol-map` / `sig-digest` / `route-map` / `query-playbook` / `dep-graph-baseline` / `extract-goal-context` は Phase A で廃止済み。

- 新規 API はビルド前に REPL `#check` で型確認
- 新規ファイル追加時は facade の `import` 関係で transitive import を確認（重複宣言エラー防止）
- 2 ファイル以上の修正は依存下流側から段階ビルド

## テスト方針

- 標準: `vanilla4`, `vanilla5`
- ストレス: `stress8` 等の大規模設定
- `#guard` は `lake build` 成功で検証完了とみなす

## シェル運用

- PowerShell 文字列置換は常に `-creplace`
- `.github/skills/` スクリプトはシェル前置なしで直接実行
- 非同期ビルドで `get_terminal_output` を連打しない
- Lean ソース検索は `grep_search` のみ（`grep` / `Select-String` による `run_in_terminal` 検索は禁止）
- 行数カウント目的の `Get-Content | Measure-Object -Line` を `run_in_terminal` で実行しない

詳細: `docs/agent/powershell-conventions.md` / `docs/agent/agent-operations-playbook.md`
