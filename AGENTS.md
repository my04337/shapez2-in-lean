# Shapez2 in Lean — エージェント運用指示

原則ベースの最上位ルールのみを置く。手続き・閾値の詳細は [docs/agent/agent-operations-playbook.md](docs/agent/agent-operations-playbook.md)。

## 1. 応答と日付

- 最終応答は日本語。サブエージェントへの指示は英語可
- 日付 `YYYY-MM-DD` / 時刻 `hh:mm:ss`。当日が不明なら `Get-Date -Format 'yyyy-MM-dd'`
- ドキュメントの `作成日` / `最終更新` は当日ローカル日付を書く

## 2. 参照入口

作業着手時、まず対象カテゴリの README を読む。

| 領域 | 入口 |
|---|---|
| Shapez2 仕様 | [docs/shapez2/README.md](docs/shapez2/README.md) |
| Lean 一般 | [docs/lean/README.md](docs/lean/README.md) |
| S2IL コードベース | [docs/s2il/README.md](docs/s2il/README.md) |
| 計画 / アーキ | [docs/plans/README.md](docs/plans/README.md) |
| エージェント運用 | [docs/agent/README.md](docs/agent/README.md) |

新規証明計画 → [proof-plan-current-focus-guide.md](docs/agent/proof-plan-current-focus-guide.md)。
撤退・pivot → [proof-retreat-pivot-guide.md](docs/agent/proof-retreat-pivot-guide.md)。
エージェント / スキル設計 → [opus-47-design-principles.md](docs/agent/opus-47-design-principles.md)。

## 3. 品質優先順位

1. 数学的な美しさ（構造・一般性・MECE）
2. コードの美しさ（可読性・保守性）

## 4. 情報探索の最短経路

Lean のシンボル探索は **facade（`S2IL.lean` / `S2IL/<Namespace>.lean`）の冒頭目次** を出発点に、最短経路で目的に到達する。前段で見つかれば後段に進まない。

| # | 目的 | 参照 |
|---|---|---|
| 1 | モジュール入口 | facade 冒頭目次コメント |
| 2 | シンボル位置 | `grep_search`（対象 `S2IL/**/*.lean`、`_archive/` 除外） |
| 3 | sorry 状況 | `S2IL/_agent/sorry-plan.json` → `sorry-goals.md` → `sorry-cards/{symbol}.md` |
| 4 | sorry のゴール形状 | REPL で `example ... := by sorry` |
| 5 | 補完 | Lean ソースへ広めの `grep_search` |

検索ツールは `grep_search` / `file_search` を優先（Lean に対して `semantic_search` は使わない）。
`grep_search` が空ヒットの場合のみ `includeIgnoredFiles: true` で 1 回再試行する。
`_archive/pre-greenfield/` は明示指示があるまで読まない。

> 詳細閾値（Explore 委譲、`grep_search` 上限など）は playbook §「検索戦略（詳細）」。

## 5. preflight（`.lean` を読む直前）

- 該当 namespace の facade 冒頭目次を先に読む
- sorry 周辺なら REPL でゴール形状を先に確認
- 会話要約継続セッションでは、対象 sorry の「ファイル:行 / コード状態 / 次アクション / ビルド状態」が summary に揃っていればスキップ可

## 6. ドキュメント管理（シングルソース原則）

各情報の正本は 1 箇所。重複転記しない。

| 情報 | 正本 |
|---|---|
| ビルド状態・sorry 件数 | `S2IL/_agent/sorry-goals.md`（自動生成） |
| 次アクション / 手順 | `sorry-plan.json` の `next_actions` / `remaining_steps` |
| 実装設計（シグネチャ・不変量・依存） | `sorry-cards/{symbol}.md` |
| sorry 依存・blockers | `sorry-plan.json` |
| セッション経緯・発見 | `git log` |
| 数学的設計・記号定義 | `docs/plans/{name}-proof-plan.md` |

新規ドキュメントは「自動更新されるか／既存で代替できるか」を確認してから作る。

## 7. 証明作業の原則

- 新規補題・仮説は証明前に反例検証（`lean-counterexample` / `by plausible` / `#eval`）
- 既存 sorry は `sorry-plan.json` → `sorry-goals.md` → 当該 sorry-card の順で確認
- 新規 `theorem` / `lemma` 記述前に REPL `#check` / `example ... := by sorry` で型を確認し、補題名は REPL 通過後に確定する
- `intro` / `rintro` 前に REPL でゴール形状を確認する
- REPL → `.lean` 移植は `transplant-proof.ps1`（bare `simp` は `-SimpStabilize`）
- 完了済み補題は本文を読まず REPL `#check` で型のみ確認

### 行き詰まったときの必須 3 ステップ

「複雑そう」という推論だけで撤退しない。順に実施してから pivot 判断する。

1. `lean-proof-planning` SKILL を読む
2. REPL で `example ... := by sorry` を発行しゴール形状を確認
3. `lean-sorry-investigator` エージェントで候補タクティクを試す

3 ステップ後に候補全滅 / 反例発覚 / 3 セッション or 8 アプローチ失敗のいずれかでのみ撤退する。詳細: [proof-retreat-pivot-guide.md](docs/agent/proof-retreat-pivot-guide.md)。

### sorry-cards の更新タイミング

証明済み化・`next_actions` 変化・セッション末コミット前に必ず差分のみ `replace_string_in_file` で更新する。

## 8. セッションメモリ

- 1 セッション原則 2 ファイル以内（断片化禁止）
- 更新は `str_replace` / `insert`（`delete → create` サイクルは避ける）
- 要約は「現在の目的 / 読んだファイルと要点 / 次アクション」の 3 項目で書く
- 次のいずれかで必ず `/memories/session/` を更新:
  - `.lean` ファイルを 3 本以上読んだ
  - セッションターン数が 30 を超えた
  - 同じ sorry に 2 ラウンド以上タクティクを試した

詳細: [session-memory-guide.md](docs/agent/session-memory-guide.md)

## 9. Lean ビルド

- `.github/skills/lean-build/scripts/build.ps1` 経由で実行する（成功時に `S2IL/_agent/sorry-goals.md` を自動更新）
- 新規 API はビルド前に REPL `#check` で型確認
- 新規ファイル追加時は facade の transitive import を確認（重複宣言の防止）
- 2 ファイル以上の修正は依存下流側から段階的にビルド

VS Code task で `lake build` を直接叩く場合のフォロー手順は playbook §「ビルド後チェックリスト」。

## 10. テスト方針

- 標準: `vanilla4`, `vanilla5`
- ストレス: `stress8` 等の大規模設定
- `#guard` は `lake build` 成功で検証完了とみなす

## 11. シェル運用

- PowerShell 文字列置換は常に `-creplace`
- `.github/skills/` のスクリプトはシェル前置なしで直接実行する
- Lean ソース検索は `grep_search` を使う（`grep` / `Select-String` の `run_in_terminal` 経由検索は避ける）
- 行数カウントは `grep_search` のヒット件数や `read_file` で済ませる

詳細: [powershell-conventions.md](docs/agent/powershell-conventions.md) / [agent-operations-playbook.md](docs/agent/agent-operations-playbook.md)
