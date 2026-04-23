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

次の順で探し、前段で見つかったら後段には進まない:

| # | 目的 | 参照先 |
|---|---|---|
| 1 | シンボル名で位置特定 | `grep_search(includePattern="S2IL/_agent/symbol-map.jsonl", query='"symbol":".*名前')` → `line` / `endLine` で `read_file` |
| 2 | ファイル 1 本の全体構造（200 行超） | `S2IL/_agent/sig-digest/<dotted-module>.md` |
| 3 | sorry 周辺の候補補題 | sorry-card の「候補補題（事前抽出）」→ なければ `.github/skills/lean-build/scripts/extract-goal-context.ps1 -File <f> -Line <n>` |
| 4 | Operation 配下の探索 | `S2IL/_agent/route-map.json` |
| 5 | タスク種別別レシピ | `S2IL/_agent/query-playbook.json` |
| 6 | sorry 状況 | `sorry-plan.json` → `sorry-goals.md` → `sorry-cards/{symbol}.md` |
| 7 | それでも不足 | Lean ソースへ `grep_search`（Lean 直 grep は symbol-map 経由後に限る） |

Lean では `semantic_search` を使わない。検索系は `grep_search` / `file_search` を優先。
`grep_search` が `No matches found` のときは `includeIgnoredFiles: true` で 1 回だけ再試行する。

### preflight チェックリスト

`.lean` ファイルを `read_file` する直前に次を確認する:

- [ ] シンボル名が既知なら symbol-map.jsonl を先に参照したか
- [ ] 200 行超のファイルは sig-digest を先に read したか（直近 3 ターン以内に該当 sig-digest を read していない場合）
- [ ] sorry 周辺の補題調査は sorry-card の Preflight 行 / extract-goal-context.ps1 を先に使ったか
- [ ] 会話要約継続セッションで、対象 sorry の「ファイル:行 / コード状態 / 次アクション / ビルド状態」が summary に揃っていれば sig-digest スキップ可

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
- 完了済み補題は本文を読まず `symbol-map.jsonl` の `sig` で型だけ確認
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
| `sig-digest/*.md` | ファイル概観・宣言行インデックス |
| `symbol-map.jsonl` | シンボル名 → `line` / `endLine` / `digest` |
| `sorry-goals.md` | sorry 宣言シグネチャ |
| `sorry-cards/*.md` の候補補題セクション | extract-goal-context 出力の事前埋込 |

手動起動スクリプト（デバッグ用）は [`docs/agent/agent-operations-playbook.md`](docs/agent/agent-operations-playbook.md) 参照。

- 新規 API はビルド前に REPL `#check` で型確認
- 新規ファイル追加時は `route-map.json` で transitive import を確認（重複宣言エラー防止）
- 2 ファイル以上の修正は依存下流側から段階ビルド
- `Verification/` に新規スクリプトを作る前は同種の既存スクリプトを 1 本読む

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
